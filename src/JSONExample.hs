{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module JSONExample where

import Control.Lens (makePrisms, _1, _2, _3, _head, _tail)
import Data.Char
import Data.Profunctor (lmap)
import Freer
import Text.Printf (printf)

data JSON = Object [(String, JSON)] | Array [JSON] | String String | Number Number | Bool Bool | Null
  deriving (Eq, Ord, Show, Read)

data Number = Int String | IntFrac String String | IntExp String String | IntFracExp String String String
  deriving (Eq, Ord, Show, Read)

makePrisms ''JSON
makePrisms ''Number

token :: Char -> FR b ()
token s = labelled [(['\'', s, '\''], pure ())]

label :: String -> FR b ()
label s = labelled [(s, pure ())]

-- start = array | object ;
start :: FR String String
start =
  labelled
    [ ("array", array),
      ("object", object)
    ]

-- object = "{" "}" | "{" members "}" ;
object :: FR String String
object =
  labelled
    [ ( "'{' members '}'",
        do
          b1 <- lmap (take 1) (exact "{")
          ms <- lmap (drop 1) members
          b2 <- lmap (take 1 . drop (1 + length ms)) (exact "}")
          pure (b1 ++ ms ++ b2)
      ),
      ("'{' '}'", lmap (take 2) (exact "{}"))
    ]

-- members = pair | pair ',' members ;
members :: FR String String
members =
  labelled
    [ ("pair", pair),
      ( "pair ',' members",
        do
          p <- pair
          c <- lmap (take 1 . drop (length p)) (exact ",")
          ps <- lmap (drop (length p + 1)) members
          pure (p ++ c ++ ps)
      )
    ]

-- pair = string ':' value ;
pair :: FR String String
pair = do
  s <- string
  c <- lmap (take 1 . drop (length s)) (exact ":")
  v <- lmap (drop (length s + 1)) value
  pure (s ++ c ++ v)

-- array = "[" elements "]" | "[" "]" ;
array :: FR String String
array =
  labelled
    [ ( "'[' elements ']'",
        do
          b1 <- lmap (take 1) (exact "[")
          ms <- lmap (drop 1) elements
          b2 <- lmap (take 1 . drop (1 + length ms)) (exact "]")
          pure (b1 ++ ms ++ b2)
      ),
      ("'[' ']'", lmap (take 2) (exact "[]"))
    ]

-- elements = value ',' elements | value ;
elements :: FR String String
elements =
  labelled
    [ ("value", value),
      ( "value ',' elements",
        do
          el <- value
          c <- lmap (take 1 . drop (length el)) (exact ",")
          es <- lmap (drop (length el + 1)) elements
          pure (el ++ c ++ es)
      )
    ]

-- value = "f" "a" "l" "s" "e" | string | array | "t" "r" "u" "e" | number | object | "n" "u" "l" "l" ;
value :: FR String String
value =
  labelled
    [ ("false", lmap (take 5) (exact "false")),
      ("string", string),
      ("array", array),
      ("number", number),
      ("true", lmap (take 4) (exact "true")),
      ("object", object),
      ("null", lmap (take 4) (exact "null"))
    ]

-- string = "\"" "\"" | "\"" chars "\"" ;
string :: FR String String
string =
  labelled
    [ ("'\"' '\"'", lmap (take 2) exact "\"\""),
      ( "'\"' chars '\"'",
        do
          q1 <- lmap (take 1) (exact ['"'])
          cs <- lmap (drop 1) chars
          q2 <- lmap (take 1 . drop (1 + length cs)) (exact ['"'])
          pure (q1 ++ cs ++ q2)
      )
    ]

-- chars = char_ chars | char_ ;
chars :: FR String String
chars =
  labelled
    [ ("char_ chars", (:) <$> tryFocus _head char_ <*> tryFocus _tail chars),
      ("char_", (: []) <$> tryFocus _head char_)
    ]

-- char_ = digit | unescapedspecial | letter | escapedspecial ;
char_ :: FR Char Char
char_ =
  labelled
    [ ("digit", digit),
      ("unescapedspecial", unescapedspecial),
      ("letter", letter)
      -- ("escapedspecial", escapedspecial) -- FIXME: I don't know how to fix this.
    ]

-- letter = "y" | "c" | "K" | "T" | "s" | "N" | "b" | "S" | "R" | "Y" | "C" | "B" | "h" | "J" | "u" | "Q" | "d" | "k" | "t" | "V" | "a" | "x" | "G" | "v" | "D" | "m" | "F" | "w" | "i" | "n" | "L" | "p" | "q" | "W" | "A" | "X" | "I" | "O" | "l" | "P" | "H" | "e" | "f" | "o" | "j" | "Z" | "g" | "E" | "r" | "M" | "z" | "U" ;
letter :: FR Char Char
letter = oneof (map (\c -> token c >> exact c) ['y', 'c', 'K', 'T', 's', 'N', 'b', 'S', 'R', 'Y', 'C', 'B', 'h', 'J', 'u', 'Q', 'd', 'k', 't', 'V', 'a', 'x', 'G', 'v', 'D', 'm', 'F', 'w', 'i', 'n', 'L', 'p', 'q', 'W', 'A', 'X', 'I', 'O', 'l', 'P', 'H', 'e', 'f', 'o', 'j', 'Z', 'g', 'E', 'r', 'M', 'z', 'U'])

-- unescapedspecial = "/" | "+" | ":" | "@" | "$" | "!" | "'" | "(" | "," | "." | ")" | "-" | "#" | "_" | ... "%" | "=" | ">" | "<" | "{" | "}" | "^" | "*" | "|" | ";" | " " ; -- NOTE: I had to add some things
unescapedspecial :: FR Char Char
unescapedspecial = oneof (map (\c -> token c >> exact c) ['/', '+', ':', '@', '$', '!', '\'', '(', ',', '.', ')', '-', '#', '_', '%', '=', '>', '<', '{', '}', '^', '*', '|', ';', ' '])

-- escapedspecial = "\\b" | "\\n" | "\\r" | "\\/" | "\\u" hextwobyte | "\\\\" | "\\t" | "\\\"" | "\\f" ;
escapedspecial :: FR Char Char
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
hextwobyte :: FR Char Char
hextwobyte = comap (\c -> if c == '\"' then Nothing else Just c) $ do
  a <- lmap ((!! 0) . printf "%04X" . ord) hexdigit
  b <- lmap ((!! 1) . printf "%04X" . ord) hexdigit
  c <- lmap ((!! 2) . printf "%04X" . ord) hexdigit
  d <- lmap ((!! 3) . printf "%04X" . ord) hexdigit <* token ';'
  pure (chr (16 * 16 * 16 * digitToInt a + 16 * 16 * digitToInt b + 16 * digitToInt c + digitToInt d))

-- hexdigit = hexletter | digit ;
hexdigit :: FR Char Char
hexdigit = labelled [("hexletter", hexletter), ("digit", digit)]

-- hexletter = "f" | "e" | "F" | "A" | "D" | "a" | "B" | "d" | "E" | "c" | "b" | "C" ;
hexletter :: FR Char Char
hexletter = oneof (map (\c -> token c >> exact c) ['f', 'e', 'F', 'A', 'D', 'a', 'B', 'd', 'E', 'c', 'b', 'C'])

-- number = int_ frac exp | int_ frac | int_ exp | int_ ;
number :: FR String String
number =
  labelled
    [ ( "int_ frac exp",
        do
          i <- int_
          f <- lmap (drop (length i)) frac
          ex <- lmap (drop (length i + length f)) expo
          pure (i ++ f ++ ex)
      ),
      ( "int_ frac",
        do
          i <- int_
          f <- lmap (drop (length i)) frac
          pure (i ++ f)
      ),
      ( "int_ exp",
        do
          i <- int_
          ex <- lmap (drop (length i)) expo
          pure (i ++ ex)
      ),
      ("int_", int_)
    ]

-- int_ = nonzerodigit digits | "-" digit digits | digit | "-" digit ;
int_ :: FR String String
int_ =
  labelled
    [ ("nonzero digits", (:) <$> tryFocus _head nonzerodigit <*> tryFocus _tail digits),
      ("'-' digit digits", (:) <$> tryFocus _head (exact '-') <*> tryFocus _tail ((:) <$> tryFocus _head digit <*> tryFocus _tail digits)),
      ( "'-' digit",
        (\x y -> x : [y])
          <$> tryFocus _head (exact '-')
          <*> tryFocus (_tail . _head) digit
      ),
      ("digit", (: []) <$> tryFocus _head digit)
    ]

-- frac = "." digits ;
frac :: FR String String
frac = label "'.' digits" >> (:) <$> tryFocus _head (exact '.') <*> tryFocus _tail digits

-- exp = e digits ;
expo :: FR String String
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
digits :: FR String String
digits =
  labelled
    [ ("digit digits", (:) <$> tryFocus _head digit <*> tryFocus _tail digits),
      ("digit", (: []) <$> tryFocus _head digit)
    ]

-- digit = nonzerodigit | "0" ;
digit :: FR Char Char
digit =
  labelled [("nonzerodigit", nonzerodigit), ("'0'", exact '0')]

-- nonzerodigit = "3" | "4" | "7" | "8" | "1" | "9" | "5" | "6" | "2" ;
nonzerodigit :: FR Char Char
nonzerodigit =
  oneof (map (\c -> token c >> exact c) ['3', '4', '7', '8', '1', '9', '5', '6', '2'])

-- e = "e" | "E" | "e" "-" | "E" "-" | "E" "+" | "e" "+" ;
e :: FR String String
e =
  labelled
    [ ("'e'", lmap (take 1) (exact "e")),
      ("'E'", lmap (take 1) (exact "E")),
      ("'e-'", lmap (take 2) (exact "e-")),
      ("'E-'", lmap (take 2) (exact "E-")),
      ("'e+'", lmap (take 2) (exact "e+")),
      ("'E+'", lmap (take 2) (exact "E+"))
    ]