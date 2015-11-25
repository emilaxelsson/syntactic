import Test.Tasty

import qualified NanoFeldsparTests
import qualified WellScopedTests
import qualified MonadTests
import qualified TH

tests = testGroup "AllTests"
    [ NanoFeldsparTests.tests
    , WellScopedTests.tests
    , MonadTests.tests
    ]

main = do
    TH.main
    defaultMain tests

