#include "llvm/CodeGen/TargetLowering.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Pass.h"
using namespace llvm;

class MultiCanary : public FunctionPass {
public:
  static char ID;
  MultiCanary(): FunctionPass(ID) {}

  void getAnalysisUsage(AnalysisUsage &Info) const override;

  bool runOnFunction(Function &F) override;

private:
  BasicBlock *CreateFailureBB(Function &F);
  BasicBlock *CreateValidationBB(AllocaInst *AI, BasicBlock *ParentBB, BasicBlock *SuccessBB, BasicBlock *FailBB, Function *F, unsigned nCanary, Value *CanaryTLS, unsigned PtrSize, MDNode *Weights);
  BasicBlock *CreateCanaryStoreBB(AllocaInst *AI, BasicBlock *ParentBB, BasicBlock *AfterBB, Function *F, unsigned nCanary, Value *Canary, unsigned PtrSize, MDNode *Weights);
};