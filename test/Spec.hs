import Test.Hspec
import Text.Printf

import Statix.Eval

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "core" $ do
    it "[✓] ∃ x. x = x" $ do
      check "{x} x = x" `shouldBe` True

    it "[✓] ∃ x y. x = y" $ do
      check "{x, y} x = y" `shouldBe` True

    it "[×] ∃ x. f(x) = x" $ do
      check "{x} f(x) = x" `shouldBe` False

    it "[×] ∃ x y. f(x) = y" $ do
      check "{x, y} f(x) = y" `shouldBe` True
