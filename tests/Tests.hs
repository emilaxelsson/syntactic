import Test.Tasty

import qualified AlgorithmTests
import qualified NanoFeldsparTests
import qualified WellScopedTests
import qualified MonadTests
import qualified TH

tests = testGroup "AllTests"
    [ AlgorithmTests.tests
    , NanoFeldsparTests.tests
    , WellScopedTests.tests
    , MonadTests.tests
    ]

main = do
    TH.main
    defaultMain tests

