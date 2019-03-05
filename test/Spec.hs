import Test.Hspec
import Text.Printf

import Statix.Eval

main :: IO ()
main = hspec $ do
  corespec
  newspec

corespec :: Spec
corespec =
  describe "core" $ do
    it "[✓] ∃ x. x = x" $ do
      check "{x} x = x" `shouldBe` True

    it "[✓] ∃ x y. x = y" $ do
      check "{x, y} x = y" `shouldBe` True

    it "[×] ∃ x. f(x) = x" $ do
      check "{x} f(x) = x" `shouldBe` False

    it "[×] ∃ x y. f(x) = y" $ do
      check "{x, y} f(x) = y" `shouldBe` True

newspec :: Spec
newspec = describe "new" $ do
    it "[✓] ∃ x . new x" $ do
      check "{x} new x" `shouldBe` True

    it "[×] ∃ x . new x, new x" $ do
      check "{x} new x, new x" `shouldBe` False

    it "[✓] ∃ x y . new x, new y" $ do
      check "{x, y} new x, new y" `shouldBe` True
