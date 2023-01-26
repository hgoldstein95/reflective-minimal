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

printJSON :: JSON -> String
printJSON = concat . head . unparse start

parseJSON :: String -> JSON
parseJSON = fst . head . parse start . map (: [])

token :: Char -> FR b ()
token s = labelled [([s], pure ())]

-- start = array | object ;
start :: FR JSON JSON
start =
  oneof
    [ Array <$> tryFocus _Array array,
      Object <$> tryFocus _Object object
    ]

-- object = "{" "}" | "{" members "}" ;
object :: FR [(String, JSON)] [(String, JSON)]
object =
  oneof
    [ token '{' *> members <* token '}',
      token '{' >> token '}' >> exact []
    ]

-- members = pair | pair ',' members ;
members :: FR [(String, JSON)] [(String, JSON)]
members =
  oneof
    [ (: []) <$> comap (\case [x] -> Just x; _ -> Nothing) pair,
      (:) <$> tryFocus _head pair <*> (token ',' *> tryFocus _tail members)
    ]

-- pair = string ':' value ;
pair :: FR (String, JSON) (String, JSON)
pair = (,) <$> lmap fst string <*> (token ':' *> lmap snd value)

-- array = "[" elements "]" | "[" "]" ;
array :: FR [JSON] [JSON]
array =
  oneof
    [ token '[' >> token ']' >> exact [],
      token '[' *> elements <* token ']'
    ]

-- elements = value ',' elements | value ;
elements :: FR [JSON] [JSON]
elements =
  oneof
    [ (:) <$> tryFocus _head value <*> (token ',' *> tryFocus _tail elements),
      (: []) <$> comap (\case [x] -> Just x; _ -> Nothing) value
    ]

-- value = "f" "a" "l" "s" "e" | string | array | "t" "r" "u" "e" | number | object | "n" "u" "l" "l" ;
value :: FR JSON JSON
value =
  oneof
    [ token 'f' >> token 'a' >> token 'l' >> token 's' >> token 'e' >> exact (Bool False),
      String <$> tryFocus _String string,
      Array <$> tryFocus _Array array,
      token 't' >> token 'r' >> token 'u' >> token 'e' >> exact (Bool True),
      Number <$> tryFocus _Number number,
      Object <$> tryFocus _Object object,
      token 'n' >> token 'u' >> token 'l' >> token 'l' >> exact Null
    ]

-- string = "\"" "\"" | "\"" chars "\"" ;
string :: FR String String
string =
  oneof
    [ token '"' >> token '"' >> exact "",
      token '"' *> chars <* token '"'
    ]

-- chars = char_ chars | char_ ;
chars :: FR String String
chars =
  oneof
    [ (:) <$> tryFocus _head char_ <*> tryFocus _tail chars,
      (: []) <$> comap (\case [x] -> Just x; _ -> Nothing) char_
    ]

-- char_ = digit | unescapedspecial | letter | escapedspecial ;
char_ :: FR Char Char
char_ = oneof [digit, unescapedspecial, letter, escapedspecial]

-- letter = "y" | "c" | "K" | "T" | "s" | "N" | "b" | "S" | "R" | "Y" | "C" | "B" | "h" | "J" | "u" | "Q" | "d" | "k" | "t" | "V" | "a" | "x" | "G" | "v" | "D" | "m" | "F" | "w" | "i" | "n" | "L" | "p" | "q" | "W" | "A" | "X" | "I" | "O" | "l" | "P" | "H" | "e" | "f" | "o" | "j" | "Z" | "g" | "E" | "r" | "M" | "z" | "U" ;
letter :: FR Char Char
letter = oneof (map (\c -> token c *> exact c) ['y', 'c', 'K', 'T', 's', 'N', 'b', 'S', 'R', 'Y', 'C', 'B', 'h', 'J', 'u', 'Q', 'd', 'k', 't', 'V', 'a', 'x', 'G', 'v', 'D', 'm', 'F', 'w', 'i', 'n', 'L', 'p', 'q', 'W', 'A', 'X', 'I', 'O', 'l', 'P', 'H', 'e', 'f', 'o', 'j', 'Z', 'g', 'E', 'r', 'M', 'z', 'U'])

-- unescapedspecial = "/" | "+" | ":" | "@" | "$" | "!" | "'" | "(" | "," | "." | ")" | "-" | "#" | "_" | ... "%" | "=" | ">" | "<" | "{" | "}" | "^" | "*" | "|" | ";" | " " ; -- NOTE: I had to add some things
unescapedspecial :: FR Char Char
unescapedspecial = oneof (map (\c -> token c *> exact c) ['/', '+', ':', '@', '$', '!', '\'', '(', ',', '.', ')', '-', '#', '_', '%', '=', '>', '<', '{', '}', '^', '*', '|', ';', ' '])

-- escapedspecial = "\\b" | "\\n" | "\\r" | "\\/" | "\\u" hextwobyte | "\\\\" | "\\t" | "\\\"" | "\\f" ;
escapedspecial :: FR Char Char
escapedspecial =
  oneof
    [ token '\\' >> token 'b' >> exact '\b',
      token '\\' >> token 'n' >> exact '\n',
      token '\\' >> token 'r' >> exact '\r',
      token '\\' >> token '/' >> exact '/',
      token '\\' >> token 'u' >> hextwobyte,
      token '\\' >> token '\\' >> exact '\\',
      token '\\' >> token 't' >> exact '\t',
      token '\\' >> token '"' >> exact '"',
      token '\\' >> token 'f' >> exact '\f'
    ]

-- hextwobyte = hexdigit hexdigit hexdigit hexdigit ;
hextwobyte :: FR Char Char
hextwobyte = do
  a <- lmap ((!! 0) . printf "%04X" . ord) hexdigit
  b <- lmap ((!! 1) . printf "%04X" . ord) hexdigit
  c <- lmap ((!! 2) . printf "%04X" . ord) hexdigit
  d <- lmap ((!! 3) . printf "%04X" . ord) hexdigit <* token ';'
  pure (chr (16 * 16 * 16 * digitToInt a + 16 * 16 * digitToInt b + 16 * digitToInt c + digitToInt d))

-- hexdigit = hexletter | digit ;
hexdigit :: FR Char Char
hexdigit = oneof [hexletter, digit]

-- hexletter = "f" | "e" | "F" | "A" | "D" | "a" | "B" | "d" | "E" | "c" | "b" | "C" ;
hexletter :: FR Char Char
hexletter = oneof (map (\c -> token c *> exact c) ['f', 'e', 'F', 'A', 'D', 'a', 'B', 'd', 'E', 'c', 'b', 'C'])

-- number = int_ frac exp | int_ frac | int_ exp | int_ ;
number :: FR Number Number
number =
  oneof
    [ IntFracExp <$> tryFocus (_IntFracExp . _1) int_ <*> tryFocus (_IntFracExp . _2) frac <*> tryFocus (_IntFracExp . _3) expo,
      IntFrac <$> tryFocus (_IntFrac . _1) int_ <*> tryFocus (_IntFrac . _2) frac,
      IntExp <$> tryFocus (_IntExp . _1) int_ <*> tryFocus (_IntExp . _2) expo,
      Int <$> tryFocus _Int int_
    ]

-- int_ = nonzerodigit digits | "-" digit digits | digit | "-" digit ;
int_ :: FR String String
int_ =
  oneof
    [ (:) <$> tryFocus _head nonzerodigit <*> tryFocus _tail digits,
      (:) <$> tryFocus _head (token '-' *> exact '-') <*> tryFocus _tail ((:) <$> tryFocus _head digit <*> tryFocus _tail digits),
      (\x y -> x : [y])
        <$> tryFocus _head (token '-' *> exact '-')
        <*> comap (\case [x] -> Just x; _ -> Nothing) digit,
      (: []) <$> comap (\case [x] -> Just x; _ -> Nothing) digit
    ]

-- frac = "." digits ;
frac :: FR String String
frac = token '.' *> digits

-- exp = e digits ;
expo :: FR String String
expo = (++) <$> comap (fmap fst . splite) e <*> comap (fmap snd . splite) digits
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
  oneof
    [ (:) <$> tryFocus _head digit <*> tryFocus _tail digits,
      (: []) <$> comap (\case [x] -> Just x; _ -> Nothing) digit
    ]

-- digit = nonzerodigit | "0" ;
digit :: FR Char Char
digit = oneof [nonzerodigit, token '0' *> exact '0']

-- nonzerodigit = "3" | "4" | "7" | "8" | "1" | "9" | "5" | "6" | "2" ;
nonzerodigit :: FR Char Char
nonzerodigit = oneof (map (\c -> token c *> exact c) ['3', '4', '7', '8', '1', '9', '5', '6', '2'])

-- e = "e" | "E" | "e" "-" | "E" "-" | "E" "+" | "e" "+" ;
e :: FR String String
e =
  oneof
    [ token 'e' *> exact "",
      token 'E' *> exact "",
      token 'e' *> token '-' *> exact "-",
      token 'E' *> token '-' *> exact "-",
      token 'E' *> token '+' *> exact "+",
      token 'e' *> token '+' *> exact "+"
    ]