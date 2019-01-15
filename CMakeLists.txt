add_llvm_loadable_module(LLVMMultiCanary
  MultiCanary.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/MultiCanary

  PLUGIN_TOOL
  opt
)

set_target_properties(LLVMMultiCanary PROPERTIES COMPILE_FLAGS "-D__GLIBCXX_USE_CXX11_ABI=0 -fno-rtti" )