module wlprettytest where

open import Data.Char
open import Data.List as L
open import Data.Nat
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.String as S renaming (_++_ to _+++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import WLPretty

-- test words function

_ : words "" ≡ []
_ = refl

_ : words "aa" ≡ "aa" ∷ []
_ = refl

_ : words "aaa gggggg ii" ≡ "aaa" ∷ "gggggg" ∷ "ii" ∷ []
_ = refl

_ : words " ee" ≡ "ee" ∷ []
_ = refl

_ : words " ee " ≡ "ee" ∷ []
_ = refl

_ : words " ee   ttttt" ≡ "ee" ∷ "ttttt" ∷ []
_ = refl

_ : words " ee   ttttt   " ≡ "ee" ∷ "ttttt" ∷ []
_ = refl


-- test lines function

_ : lines "" ≡ []
_ = refl

_ : lines "aa" ≡ "aa" ∷ []
_ = refl

_ : lines "aaa\ngggggg ii" ≡ "aaa" ∷ "gggggg ii" ∷ []
_ = refl

_ : lines " ee" ≡ " ee" ∷ []
_ = refl

_ : lines " ee\n" ≡ " ee" ∷ []
_ = refl

_ : lines " ee\n   ttttt" ≡ " ee" ∷ "   ttttt" ∷ []
_ = refl

_ : lines "\nee   ttttt\n   " ≡ "ee   ttttt" ∷ "   " ∷ []
_ = refl


showDoc : Doc → String
showDoc Empty = "Empty "
showDoc (Char c) = Data.Char.show c
showDoc (Text l s) = "TEXT " +++ ℕshow l +++ ":" +++ s
showDoc (Line _) = "LINE "
showDoc (Cat a b) = (showDoc a +++ " :<> " +++ showDoc b)
showDoc (Nest i d) = "\nNEST " +++ ℕshow i +++ " " +++ showDoc d
showDoc (Union a b) = (showDoc a +++ " :<|> " +++ showDoc b)
showDoc (Column f) = "COLUMN "
showDoc (Nesting f) = "NESTING "

-- Tree example

data Tree : Set where
  Node : String → List Tree → Tree

{-# TERMINATING #-}
showTree     : Tree → Doc
showBracket  : List Tree → Doc
showTrees    : List Tree → Doc
showTree'    : Tree → Doc
showBracket' : List Tree → Doc
showTrees'   : List Tree → Doc

showTree (Node s ts) = group (text s <> nest (S.length s) (showBracket ts))

showBracket [] = empty
showBracket ts = enclose (text "[") (text "]") (nest 1 (showTrees ts))

showTrees [] = empty
showTrees (t ∷ []) = showTree t
showTrees (t ∷ ts) = showTree t <> text "," <> line <> showTrees ts

instance
  ppTree : Pretty Tree
  pretty {{ppTree}} = showTree
  
showTree' (Node s ts) = group (text s <> showBracket' ts)

showBracket' [] = empty
showBracket' ts = enclose lbracket rbracket (nest 2 (linebreak <> showTrees' ts))

showTrees' [] = empty
showTrees' ts = folddoc (λ x y → x <> comma <> line <> y) (L.map showTree' ts)

instance
  ppTree' : Pretty Tree
  pretty {{ppTree'}} = showTree'
  

tree : Tree
tree = Node "aaa" (
                   (Node "bbbbb" (
                                 Node "ccc" []
                                 ∷ Node "dd" []
                                 ∷ []
                                ))
                   ∷ Node "eee" []
                   ∷ (Node "ffff" (
                                  Node "gg" []
                                  ∷ Node "hhh" []
                                  ∷ Node "ii" []
                                  ∷ []
                                 ))
                   ∷ []
                 )

tree1 = Node "aaa" (
                   Node "bbbbb" []
                   ∷ Node "eee" []
                   ∷ Node "ffff" []
                   ∷ []
                 )
-- XML example

data Att : Set where
  mkAtt : String → String → Att
  
data XML : Set where
  Elt : String → List Att → List XML → XML
  Txt : String → XML

quoted : String → String
quoted s = "\"" +++ s +++ "\""

showAtt : Att → Doc
showAtt (mkAtt n v) = group (text n <> text "=" <> text (quoted v))

showTag : String → List Att → Doc
showTag n a = text n <+> nest (2 + S.length n) (folddoc (λ x y → x <> comma <> softline <> y) (L.map showAtt a))

showXMLs : List XML → Doc 

{-# TERMINATING #-}
showXML : XML → Doc
showXML (Elt n a []) = text "<" <> showTag n a <> text "/>" <> linebreak 
showXML (Elt n a c)  = text "<" <> showTag n a <> text ">" 
                       <> nest 4 (linebreak <> showXMLs c)
                       <> linebreak <> text "</" <> text n <> text ">"
showXML (Txt s) = string s -- map text (words s)

showXMLs x = fillSep (L.map showXML x)

instance
  ppXML : Pretty XML
  pretty {{ppXML}} = showXML
  
xml : XML
xml = Elt "p" (
              mkAtt "color" "red"
              ∷ mkAtt "font" "Times"
              ∷ mkAtt "size" "10"
              ∷ []
              ) (
                Txt "Here is some"
                ∷ Elt "em" [] (
                              Txt "emphasized" ∷ []
                              )
                ∷ Txt "text."
                ∷ Txt "Here is a"
                ∷ Elt "a" (
                          mkAtt "href" "http://www.eg.com/" ∷ []
                          ) (
                            Txt "link"
                            ∷ Txt "elsewhere."
                            ∷ []
                            )
                ∷ [])



open import IO

main = run (putStr StringToPrint)
  where
  StringToPrint = ""
    +++ "============================\n"
    +++ (ppretty 20 (showTree tree))
    +++ "\n============================\n"
    +++ (ppretty 10 (showTree tree))
    +++ "\n============================\n"
    +++ (ppretty 19 (showTree' tree))
    +++ "\n============================\n"
    +++ (ppretty 10 (showTree' tree))
    +++ "\n============================\n"
    +++ (ppretty 40 (showTree' tree))
    +++ "\n============================\n"
    +++ (pprint {p = ppTree} 19 tree)
    +++ "\n============================\n"
    +++ (pprint {p = ppTree'} 19 tree)
    -- +++ "\n============================\n"
    -- +++ (pretty 6 (showTree tree1))
    +++ "\n============================\n"
    +++ (pprint {p = ppXML} 10 xml)
    +++ "\n============================\n"
    +++ (pprint {p = ppXML} 20 xml)
    +++ "\n============================\n"
    +++ (pprint {p = ppXML} 40 xml)
