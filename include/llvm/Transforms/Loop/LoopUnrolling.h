#include "llvm/Pass.h"

using namespace llvm;

namespace llvm
{
    enum class LoopUnrollResult;

    class LoopUnrolling : public FunctionPass {
      public:
        static char ID;
        LoopUnrolling();

        bool runOnFunction(Function &function) override;
        void getAnalysisUsage(AnalysisUsage &analysisUsage) const override;
      private:
        LoopUnrollResult tryToUnrollLoop();
    };
}
