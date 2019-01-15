#include "llvm/CodeGen/StackProtector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetLowering.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/User.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "MultiCanary.h"
#include <string>

using namespace llvm;

void MultiCanary::getAnalysisUsage(AnalysisUsage &Info) const {
  Info.addRequired<TargetPassConfig>();
}

bool MultiCanary::runOnFunction(Function &F) {
  bool modified = false;

  Module *M = F.getParent();
  auto &DL = M->getDataLayout();
  TargetMachine *TM = &getAnalysis<TargetPassConfig>().getTM<TargetMachine>();
  const TargetLoweringBase *TLI = TM->getSubtargetImpl(F)->getTargetLowering();

  SmallVector<AllocaInst *, 16> CanaryAIs;
  SmallVector<AllocaInst *, 16> AddedAIs;

  IRBuilder<> B(F.getEntryBlock()->getContext());

  BasicBlock *Entry = F.getEntryBasicBlock();
  for (auto &I : Entry) {
    // Canaryの配置
    if (AllocaInst *AI = dyn_cast<AllocaInst>(&I)) {
      errs() << "---- found AllocaInst ----\n";

      // skip MultiCanary related allocas.
      if (AI->getName().startswith(StringRef("MultiCanary"))) continue;

      AI->dump();

      unsigned CanarySize = AI->getMultiCanarySize();
      AllocaInst *CanaryAI;
      if (CanarySize == 0) { // use the default size
        // %2 = alloca i8* (use i8* instead of i8 to be compatible with both of 32/64bit environment)
        CanaryAI = B.CreateAlloca(B.getInt8PtrTy(), nullptr, "MultiCanaryAlloca");
      } else { // use the specified size
        unsigned PtrSize = DL.getTypeAllocSize(B.getInt8PtrTy());
        assert(CanarySize % PtrSize == 0 && "Size of canary must be a multiple of that of i8*");
        CanaryAI = B.CreateAlloca(B.getInt8PtrTy(), ConstantInt::get(B.getInt32Ty(), CanarySize / PtrSize), "MultiCanaryAlloca");
      }

      CanaryAIs.push_back(CanaryAI);
      AddedAIs.push_back(&AI);
    }
  }

  // Call intrinsics
  for (unsigned i = 0; i < CanaryAIs.size(); ++i) {
    AllocaInst *CanaryAI = CanaryAIs[i];
    AllocaInst *BufferAI = AddedAIs[i];

    Value *Canary = TLI->getIRStackGuard(B);
    LoadInst *LI = B.CreateLoad(Canary, "MultiCanaryLoad");

    CallInst *CI = CallInst::Create(Intrinsic::getDeclaration(M, Intrinsic::multicanary, {AI->getType()}), {LI, CanaryAI, AI});
  }

  // Store
  BasicBlock *StoreNextBB = F.getEntryBlock();
  for (unsigned i = 0; i < CanaryAIs.size(); ++i) {
    AllocaInst *BufferAI = AddedAIs[i];
    if (BufferAI->getMultiCanarySize() == 0) continue;

    AllocaInst *CanaryAI = CanaryAIs[i];

    BasicBlock *StoreBB = CreateCanaryStoreBB(AI, &BB, AfterBB, &F, nCanary, LI, Weights);
    if (i == 0) B.CreateBr(StoreNextBB);
  }

  // Canaryの検証
  for (auto &BB : F) {
    errs() << "--------- " << BB.getName() << "--------" << '\n';

    // MultiCanaryReturnの後ろに任意の数字がつく(1, 2, 3...)
    // どういう仕組みかValueの実装を読んでもよくわからなかった
    // (Value.cpp: Value::setName参照)
    if (BB.getName().startswith(StringRef("MultiCanary"))) continue;

    for (auto &I : BB) {
      if (auto *RI = dyn_cast<ReturnInst>(&I)) {
        if (CanaryAIs.size() == 0) continue;
        errs() << "Found ReturnInst!\n";

        // MSVC CRTではCanaryチェック用の関数が用意されているのでそれを呼び出す
        if (Value *GuardCheck = TLI->getSSPStackGuardCheck(*M)) {
          IRBuilder<> B(RI);
          llvm::Function *Function = cast<llvm::Function>(GuardCheck);
          for (AllocaInst *AI : CanaryAIs) {
            LoadInst *Guard = B.CreateLoad(AI, true, "Guard");
            CallInst *Call = B.CreateCall(GuardCheck, {Guard});
            Call->setAttributes(Function->getAttributes());
            Call->setCallingConv(Function->getCallingConv());
          }
        } else {
          BasicBlock *FailBB = CreateFailureBB(F);

          BasicBlock *NextCheckBB = BasicBlock::Create(BB.getContext(), "MultiCanaryReturn", &F);
          BasicBlock *FirstCheckBB = NextCheckBB;

          DominatorTreeWrapperPass *DTWP = getAnalysisIfAvailable<DominatorTreeWrapperPass>();
          DominatorTree *DT = DTWP ? &DTWP->getDomTree() : nullptr;
          if (DT && DT->isReachableFromEntry(&BB)) {
            // BB is a dominator of FirstCheckBB.
            DT->addNewBlock(FirstCheckBB, &BB);
          }

          for (auto AI : CanaryAIs) {
            BasicBlock *CurrentBB = NextCheckBB;
            IRBuilder<> B(CurrentBB);

            // stackにあるcanaryを読み込む
            LoadInst *LoadCanaryStack = B.CreateLoad(AI, true, "CanaryCheckStackLoad");

            // TLSにあるcanaryを読み込む
            Value *CanaryTLS = TLI->getIRStackGuard(B);
            LoadInst *LoadCanaryTLS = B.CreateLoad(CanaryTLS, true, "CanaryCheckTLSLoad");

            auto SuccessProb = BranchProbabilityInfo::getBranchProbStackProtector(true);
            auto FailureProb = BranchProbabilityInfo::getBranchProbStackProtector(false);
            MDNode *Weights = MDBuilder(F.getContext())
                                .createBranchWeights(SuccessProb.getNumerator(), FailureProb.getNumerator());

            NextCheckBB = BasicBlock::Create(CurrentBB->getContext(), "MultiCanaryReturn", &F);

            if (!AI->isArrayAllocation()) {
              Value *Cmp = B.CreateICmpEQ(LoadCanaryTLS, LoadCanaryStack);
              B.CreateCondBr(Cmp, NextCheckBB, FailBB, Weights);
            } else {
              BasicBlock *ValidationBB = CreateValidationBB(AI, CurrentBB, NextCheckBB, FailBB, &F, cast<ConstantInt>(AI->getArraySize())->getZExtValue(), LoadCanaryTLS, Weights);
              B.CreateBr(ValidationBB);
            }

            // if (DT && DT->isReachableFromEntry(&BB)) {
            //   DT->addNewBlock(NextCheckBB, CurrentBB);
            //   DT->addNewBlock(FailBB, CurrentBB);
            // }
          }

          // FIXME: 最初のCanary検証BasicBlockを前のBasicBlockとマージすると良さそう
          // でも後ろの最適化でよしなにやってくれそうな気もする

          // 最後のBasicBlockにReturnInstを追加
          NextCheckBB->getInstList().push_back(RI->clone());

          // もともとのBBからretする代わりにMultiCanaryのチェックに飛んでくるようにする
          ReplaceInstWithInst(RI, BranchInst::Create(FirstCheckBB));
        }

        modified = true;
        break; // ReturnInst以降にどのような命令が入るか？多分入らない(StackProtectorではTerminatorがReturnInstだったら､という形で見ているので)
      }

    }
  }

  return modified;
}

// Canary配列の要素にに実際のCanary値をLoadするBBを追加する
BasicBlock *MultiCanary::CreateCanaryStoreBB(AllocaInst *AI, BasicBlock *ParentBB, BasicBlock *AfterBB, Function *F, unsigned nCanary, Value *Canary, MDNode *Weights) {
  BasicBlock *HeadBB = BasicBlock::Create(ParentBB->getContext(), "MultiCanaryStore", F);
  IRBuilder<> HB(HeadBB);

  Value *Offset = HB.CreateAlloca(HB.getInt64Ty());
  HB.CreateStore(ConstantInt::get(HB.getInt64Ty(), 0), Offset);

  // FIXME: ループもうちょっと簡単に作れないのか
  BasicBlock *LoopHeadBB = BasicBlock::Create(HeadBB->getContext(), "MultiCanaryStoreLoopHead", F);
  IRBuilder<> LHB(LoopHeadBB);
  HB.CreateBr(LoopHeadBB);
  Value *Curr = LHB.CreateLoad(Offset);
  Value *CmpI = LHB.CreateICmpSLT(Curr, ConstantInt::get(LHB.getInt64Ty(), nCanary));

  BasicBlock *LoopBodyBB = BasicBlock::Create(LoopHeadBB->getContext(), "MultiCanaryStoreLoop", F);
  // FIXME: Weightsを単なるループの終了判定につけるのは間違っていそう
  LHB.CreateCondBr(CmpI, LoopBodyBB, AfterBB, Weights);
  IRBuilder<> LB(LoopBodyBB);

  Value *OffsetLoad = LB.CreateLoad(Offset, "MultiCanaryStoreOffsetLoad");
  Value *IntAddr = LB.CreatePtrToInt(AI, LB.getInt64Ty());
  Value *IntDest = LB.CreateAdd(IntAddr, OffsetLoad);
  Value *PtrDest = LB.CreateIntToPtr(IntDest, PointerType::get(LB.getInt8PtrTy(), 0));

  LB.CreateStore(Canary, PtrDest, true);

  Value *NewOffset = LB.CreateAdd(Curr, ConstantInt::get(LB.getInt64Ty(), 1));
  LB.CreateStore(NewOffset, Offset);
  LB.CreateBr(LoopHeadBB);

  return HeadBB;
}

// Canary配列内の値がすべてTLSのそれと一致するか検証するBBを追加する
BasicBlock *MultiCanary::CreateValidationBB(AllocaInst *AI, BasicBlock *ParentBB, BasicBlock *SuccessBB, BasicBlock *FailBB, Function *F, unsigned nCanary, Value *CanaryTLS, MDNode *Weights) {
  BasicBlock *HeadBB = BasicBlock::Create(ParentBB->getContext(), "MultiCanaryValidate", F);
  IRBuilder<> HB(HeadBB);

  Value *Offset = HB.CreateAlloca(HB.getInt64Ty());
  HB.CreateStore(ConstantInt::get(HB.getInt64Ty(), 0), Offset);

  // FIXME: ループもうちょっと簡単に作れないのか
  BasicBlock *LoopHeadBB = BasicBlock::Create(HeadBB->getContext(), "MultiCanaryValidationLoopHead", F);
  IRBuilder<> LHB(LoopHeadBB);
  HB.CreateBr(LoopHeadBB);
  Value *Curr = LHB.CreateLoad(Offset);
  Value *CmpI = LHB.CreateICmpSLT(Curr, ConstantInt::get(LHB.getInt64Ty(), nCanary));
  // FIXME: Weightsを単なるループの終了判定につけるのは間違っていそう

  BasicBlock *LoopBodyBB = BasicBlock::Create(HeadBB->getContext(), "MultiCanaryValidationLoop", F);
  LHB.CreateCondBr(CmpI, LoopBodyBB, SuccessBB, Weights);
  IRBuilder<> LB(LoopBodyBB);

  Value *OffsetLoad = LB.CreateLoad(Offset, "MultiCanaryValidationOffsetLoad");

  Value *IntAddr = LB.CreatePtrToInt(AI, LB.getInt64Ty());
  Value *IntDest = LB.CreateAdd(IntAddr, OffsetLoad);
  Value *PtrDest = LB.CreateIntToPtr(IntDest, PointerType::get(LB.getInt8PtrTy(), 0));
  Value *CanaryElm = LB.CreateLoad(PtrDest);

  // Value *Idxs[2] = {ConstantInt::get(LB.getInt32Ty(), 0), OffsetLoad};
  // Value *CanaryElm = LB.CreateGEP(AI, Idxs, "MultiCanaryValidationGEP");
  Value *Cmp = LB.CreateICmpEQ(CanaryElm, CanaryTLS);

  Value *NewOffset = LB.CreateAdd(Curr, ConstantInt::get(LB.getInt64Ty(), 1));
  LB.CreateStore(NewOffset, Offset);
  LB.CreateCondBr(Cmp, LoopHeadBB, FailBB, Weights);

  return HeadBB;
}

BasicBlock *MultiCanary::CreateFailureBB(Function &F) {
  Module *M = F.getParent();

  // Fの最後にBBを追加する
  BasicBlock *FailBB = BasicBlock::Create(F.getContext(), "MultiCanaryFail", &F);
  IRBuilder<> B(FailBB);

  // FIXME: StackChkFail以外に飛ばす？, どの関数のどういう変数かという情報は必要そう
  Constant *StackChkFail = M->getOrInsertFunction("__stack_chk_fail", Type::getVoidTy(F.getContext()));
  B.CreateCall(StackChkFail, {});

  B.CreateUnreachable();

  return FailBB;
}

char MultiCanary::ID = 0;
static RegisterPass<MultiCanary> X("multicanary", "MultiCanary function", false, false);