{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module JSONTypedExample where

import Control.Lens (Prism', makePrisms, prism, _1, _2, _3, _head, _tail)
import Data.Char
import Freer
import Text.Printf (printf)

token :: Char -> Reflective b ()
token s = labelled [(['\'', s, '\''], pure ())]

label :: String -> Reflective b ()
label s = labelled [(s, pure ())]

_singleton :: Prism' [a] a
_singleton = prism (: []) $ \case
  [a] -> Right a
  _ -> Left []

data JSON = Object [(String, JSON)] | Array [JSON] | String String | Number Number | Bool Bool | Null deriving (Show, Eq, Read)

data Number = Int String | IntFrac String String | IntExp String String | IntFracExp String String String deriving (Show, Eq, Read)

makePrisms ''JSON
makePrisms ''Number

-- start = array | object ;
start :: Reflective JSON JSON
start =
  labelled
    [ ("array", Array <$> focus _Array array),
      ("object", Object <$> focus _Object object)
    ]

-- object = "{" "}" | "{" members "}" ;
object :: Reflective [(String, JSON)] [(String, JSON)]
object =
  labelled
    [ ("'{' members '}'", members),
      ("'{' '}'", exact [])
    ]

-- members = pair | pair ',' members ;
members :: Reflective [(String, JSON)] [(String, JSON)]
members =
  labelled
    [ ("pair", (: []) <$> focus _singleton pair),
      ("pair ',' members", (:) <$> focus _head pair <*> focus _tail members)
    ]

-- pair = string ':' value ;
pair :: Reflective (String, JSON) (String, JSON)
pair = (,) <$> focus _1 string <*> focus _2 value

-- array = "[" elements "]" | "[" "]" ;
array :: Reflective [JSON] [JSON]
array =
  labelled
    [ ("'[' elements ']'", elements),
      ("'[' ']'", exact [])
    ]

-- elements = value ',' elements | value ;
elements :: Reflective [JSON] [JSON]
elements =
  labelled
    [ ("value", (: []) <$> focus _singleton value),
      ("value ',' elements", (:) <$> focus _head value <*> focus _tail elements)
    ]

-- value = "f" "a" "l" "s" "e" | string | array | "t" "r" "u" "e" | number | object | "n" "u" "l" "l" ;
value :: Reflective JSON JSON
value =
  labelled
    [ ("false", exact (Bool False)),
      ("string", String <$> focus _String string),
      ("array", Array <$> focus _Array array),
      ("number", Number <$> focus _Number number),
      ("true", exact (Bool True)),
      ("object", Object <$> focus _Object object),
      ("null", exact Null)
    ]

-- string = "\"" "\"" | "\"" chars "\"" ;
string :: Reflective String String
string =
  labelled
    [ ("'\"' '\"'", exact ""),
      ("'\"' chars '\"'", chars)
    ]

-- chars = char_ chars | char_ ;
chars :: Reflective String String
chars =
  labelled
    [ ("char_", (: []) <$> focus _singleton char_),
      ("char_ chars", (:) <$> focus _head char_ <*> focus _tail chars)
    ]

-- char_ = digit | unescapedspecial | letter | escapedspecial ;
char_ :: Reflective Char Char
char_ =
  labelled
    [ ("letter", letter),
      ("digit", digit),
      ("unescapedspecial", unescapedspecial)
      -- ("escapedspecial", escapedspecial) -- FIXME: I don't know how to fix this.
    ]

-- letter = "y" | "c" | "K" | "T" | "s" | "N" | "b" | "S" | "R" | "Y" | "C" | "B" | "h" | "J" | "u" | "Q" | "d" | "k" | "t" | "V" | "a" | "x" | "G" | "v" | "D" | "m" | "F" | "w" | "i" | "n" | "L" | "p" | "q" | "W" | "A" | "X" | "I" | "O" | "l" | "P" | "H" | "e" | "f" | "o" | "j" | "Z" | "g" | "E" | "r" | "M" | "z" | "U" ;
letter :: Reflective Char Char
letter = oneof (map (\c -> token c >> exact c) (['a' .. 'z'] ++ ['A' .. 'Z']))

-- unescapedspecial = "/" | "+" | ":" | "@" | "$" | "!" | "'" | "(" | "," | "." | ")" | "-" | "#" | "_" | ... "%" | "=" | ">" | "<" | "{" | "}" | "^" | "*" | "|" | ";" | " " ; -- NOTE: I had to add some things
unescapedspecial :: Reflective Char Char
unescapedspecial = oneof (map (\c -> token c >> exact c) ['/', '+', ':', '@', '$', '!', '\'', '(', ',', '.', ')', '-', '#', '_', '%', '=', '>', '<', '{', '}', '^', '*', '|', ';', ' '])

-- escapedspecial = "\\b" | "\\n" | "\\r" | "\\/" | "\\u" hextwobyte | "\\\\" | "\\t" | "\\\"" | "\\f" ;
escapedspecial :: Reflective Char Char
escapedspecial =
  labelled
    [ ("'\\b'", exact '\b'),
      ("'\\n'", exact '\n'),
      ("'\\r'", exact '\r'),
      ("'\\/'", exact '/'),
      ("'\\u' hextwobyte", hextwobyte),
      ("'\\\\'", exact '\\'),
      ("'\\t'", exact '\t'),
      ("'\\\"", exact '\"'),
      ("'\\f'", exact '\f')
    ]

-- hextwobyte = hexdigit hexdigit hexdigit hexdigit ;
hextwobyte :: Reflective Char Char
hextwobyte = comap (\c -> if c == '\"' then Nothing else Just c) $ do
  a <- lmap ((!! 0) . printf "%04X" . ord) hexdigit
  b <- lmap ((!! 1) . printf "%04X" . ord) hexdigit
  c <- lmap ((!! 2) . printf "%04X" . ord) hexdigit
  d <- lmap ((!! 3) . printf "%04X" . ord) hexdigit <* token ';'
  pure (chr (16 * 16 * 16 * digitToInt a + 16 * 16 * digitToInt b + 16 * digitToInt c + digitToInt d))

-- hexdigit = hexletter | digit ;
hexdigit :: Reflective Char Char
hexdigit = labelled [("hexletter", hexletter), ("digit", digit)]

-- hexletter = "f" | "e" | "F" | "A" | "D" | "a" | "B" | "d" | "E" | "c" | "b" | "C" ;
hexletter :: Reflective Char Char
hexletter = oneof (map (\c -> token c >> exact c) ['f', 'e', 'F', 'A', 'D', 'a', 'B', 'd', 'E', 'c', 'b', 'C'])

-- number = int_ frac exp | int_ frac | int_ exp | int_ ;
number :: Reflective Number Number
number =
  labelled
    [ ("int_", Int <$> focus _Int int_),
      ("int_ exp", IntExp <$> focus (_IntExp . _1) int_ <*> focus (_IntExp . _2) expo),
      ("int_ frac", IntFrac <$> focus (_IntFrac . _1) int_ <*> focus (_IntFrac . _2) frac),
      ("int_ frac exp", IntFracExp <$> focus (_IntFracExp . _1) int_ <*> focus (_IntFracExp . _2) frac <*> focus (_IntFracExp . _3) expo)
    ]

-- int_ = nonzerodigit digits | "-" digit digits | digit | "-" digit ;
int_ :: Reflective String String
int_ =
  labelled
    [ ("nonzero digits", (:) <$> focus _head nonzerodigit <*> focus _tail digits),
      ("'-' digit digits", (:) <$> focus _head (exact '-') <*> focus _tail ((:) <$> focus _head digit <*> focus _tail digits)),
      ( "'-' digit",
        (\x y -> x : [y])
          <$> focus _head (exact '-')
          <*> focus (_tail . _head) digit
      ),
      ("digit", (: []) <$> focus _head digit)
    ]

-- frac = "." digits ;
frac :: Reflective String String
frac = label "'.' digits" >> (:) <$> focus _head (exact '.') <*> focus _tail digits

-- exp = e digits ;
expo :: Reflective String String
expo = label "e digits" >> (++) <$> comap (fmap fst . splite) e <*> comap (fmap snd . splite) digits
  where
    splite ('e' : '+' : xs) = Just (['e', '+'], xs)
    splite ('e' : '-' : xs) = Just (['e', '-'], xs)
    splite ('E' : '+' : xs) = Just (['E', '+'], xs)
    splite ('E' : '-' : xs) = Just (['E', '-'], xs)
    splite ('e' : xs) = Just (['e'], xs)
    splite ('E' : xs) = Just (['E'], xs)
    splite _ = Nothing

-- digits = digit digits | digit ;
digits :: Reflective String String
digits =
  labelled
    [ ("digit", (: []) <$> focus _head digit),
      ("digit digits", (:) <$> focus _head digit <*> focus _tail digits)
    ]

-- digit = nonzerodigit | "0" ;
digit :: Reflective Char Char
digit =
  labelled [("nonzerodigit", nonzerodigit), ("'0'", exact '0')]

-- nonzerodigit = "3" | "4" | "7" | "8" | "1" | "9" | "5" | "6" | "2" ;
nonzerodigit :: Reflective Char Char
nonzerodigit =
  oneof (map (\c -> token c >> exact c) ['1', '2', '3', '4', '5', '6', '7', '8', '9'])

-- e = "e" | "E" | "e" "-" | "E" "-" | "E" "+" | "e" "+" ;
e :: Reflective String String
e =
  labelled
    [ ("'e'", lmap (take 1) (exact "e")),
      ("'E'", lmap (take 1) (exact "E")),
      ("'e-'", lmap (take 2) (exact "e-")),
      ("'E-'", lmap (take 2) (exact "E-")),
      ("'e+'", lmap (take 2) (exact "e+")),
      ("'E+'", lmap (take 2) (exact "E+"))
    ]

package :: Reflective String String
package =
  obj
    [ ("name", str),
      ("description", str),
      ( "scripts",
        obj
          [ ("start", str),
            ("build", str),
            ("test", str)
          ]
      ),
      ( "repository",
        obj
          [ ("type", str),
            ("url", str)
          ]
      ),
      ("keywords", arr str),
      ("author", str),
      ("license", str),
      ("devDependencies", keyVal str),
      ("dependencies", keyVal str)
    ]
  where
    quote s = "\"" ++ s ++ "\""
    str = string
    obj fields = do
      _ <- lmap (take 1) (exact "{")
      fs <- lmap (drop 1) (aux fields)
      _ <- lmap (take 1 . drop (1 + length fs)) (exact "}")
      pure ("{" ++ fs ++ "}")
      where
        aux [] = pure ""
        aux [pr] = assign pr
        aux (pr : fs) = do
          p <- assign pr
          _ <- lmap (take 1 . drop (length p)) (exact ",")
          vs <- lmap (drop (1 + length p)) (aux fs)
          pure (p ++ "," ++ vs)
        assign (s, val) = do
          let s' = quote s
          _ <- lmap (take (length s')) (exact s')
          _ <- lmap (take 1 . drop (length s')) (exact ":")
          v <- lmap (drop (length s' + 1)) val
          pure (s' ++ ":" ++ v)
    keyVal elt = do
      _ <- lmap (take 1) (exact "{")
      fs <- lmap (drop 1) aux
      _ <- lmap (take 1 . drop (1 + length fs)) (exact "}")
      pure ("{" ++ fs ++ "}")
      where
        aux =
          labelled
            [ ("assign", assign),
              ( "assign ',' assigns",
                do
                  el <- assign
                  _ <- lmap (take 1 . drop (length el)) (exact ",")
                  es <- lmap (drop (length el + 1)) aux
                  pure (el ++ "," ++ es)
              )
            ]
        assign = do
          s <- str
          _ <- lmap (take 1 . drop (length s)) (exact ":")
          v <- lmap (drop (length s + 1)) elt
          pure (s ++ ":" ++ v)
    arr elt = do
      _ <- lmap (take 1) (exact "[")
      fs <- lmap (drop 1) aux
      _ <- lmap (take 1 . drop (1 + length fs)) (exact "]")
      pure ("[" ++ fs ++ "]")
      where
        aux =
          labelled -- TODO Only one?
            [ ("elt", elt),
              ( "elt ',' elts",
                do
                  el <- elt
                  _ <- lmap (take 1 . drop (length el)) (exact ",")
                  es <- lmap (drop (length el + 1)) aux
                  pure (el ++ "," ++ es)
              )
            ]