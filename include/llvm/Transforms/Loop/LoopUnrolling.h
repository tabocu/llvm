#include "llvm/Pass.h"

#include <vector>

namespace llvm
{
    enum class LoopUnrollResult;

    class AssumptionCache;
    class DominatorTree;
    class Loop;
    class LoopInfo;
    class OptimizationRemarkEmitter;
    class ScalarEvolution;

    class LoopUnrolling : public FunctionPass {
      public:
        static char ID;
        LoopUnrolling();

        bool runOnFunction(Function &function) override;
        void getAnalysisUsage(AnalysisUsage &analysisUsage) const override;
      private:
        static std::vector<Loop*> getLeafLoops(Loop& rootLoop);

        static LoopUnrollResult tryToUnrollLoop(unsigned                   count,
                                                Loop&                      loop,
                                                LoopInfo&                  loopInfo,
                                                ScalarEvolution&           scalarEvolution,
                                                DominatorTree&             dominatorTree,
                                                AssumptionCache&           assumptionCache,
                                                OptimizationRemarkEmitter& optimizationRemarkEmitter);
    };
}
