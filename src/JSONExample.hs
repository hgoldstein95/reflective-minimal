module JSONExample where

import Control.Lens (_head, _tail)
import Data.Bits (xor)
import Data.Char (chr, digitToInt, ord)
import Data.Foldable (Foldable (foldl'))
import Freer (Reflective, comap, exact, focus, labelled, lmap)
import Text.Printf (printf)

token :: Char -> Reflective b ()
token s = labelled [(['\'', s, '\''], pure ())]

label :: String -> Reflective b ()
label s = labelled [(s, pure ())]

-- start = array | object ;
start :: Reflective String String
start =
  labelled
    [ ("array", array),
      ("object", object)
    ]

{-# INLINE (>>-) #-}
(>>-) :: Reflective String String -> (String -> Reflective String String) -> Reflective String String
p >>- f = do
  x <- p
  lmap (drop (length x)) (f x)

-- object = "{" "}" | "{" members "}" ;
object :: Reflective String String
object =
  labelled
    [ ( "'{' members '}'",
        lmap (take 1) (exact "{") >>- \b1 ->
          members >>- \ms ->
            lmap (take 1) (exact "}") >>- \b2 ->
              pure (b1 ++ ms ++ b2)
      ),
      ("'{' '}'", lmap (take 2) (exact "{}"))
    ]

-- members = pair | pair ',' members ;
members :: Reflective String String
members =
  labelled
    [ ("pair", pair),
      ( "pair ',' members",
        pair >>- \p ->
          lmap (take 1) (exact ",") >>- \c ->
            members >>- \ps ->
              pure (p ++ c ++ ps)
      )
    ]

-- pair = string ':' value ;
pair :: Reflective String String
pair =
  string >>- \s ->
    lmap (take 1) (exact ":") >>- \c ->
      value >>- \v ->
        pure (s ++ c ++ v)

-- array = "[" elements "]" | "[" "]" ;
array :: Reflective String String
array =
  labelled
    [ ("'[' ']'", lmap (take 2) (exact "[]")),
      ( "'[' elements ']'",
        lmap (take 1) (exact "[") >>- \b1 ->
          elements >>- \ms ->
            lmap (take 1) (exact "]") >>- \b2 ->
              pure (b1 ++ ms ++ b2)
      )
    ]

-- elements = value ',' elements | value ;
elements :: Reflective String String
elements =
  labelled
    [ ("value", value),
      ( "value ',' elements",
        value >>- \el ->
          lmap (take 1) (exact ",") >>- \c ->
            elements >>- \es ->
              pure (el ++ c ++ es)
      )
    ]

-- value = "f" "a" "l" "s" "e" | string | array | "t" "r" "u" "e" | number | object | "n" "u" "l" "l" ;
value :: Reflective String String
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
string :: Reflective String String
string =
  labelled
    [ ("'\"' '\"'", lmap (take 2) (exact "\"\"")),
      ( "'\"' chars '\"'",
        lmap (take 1) (exact ['"']) >>- \q1 ->
          chars >>- \cs ->
            lmap (take 1) (exact ['"']) >>- \q2 ->
              pure (q1 ++ cs ++ q2)
      )
    ]

-- chars = char_ chars | char_ ;
chars :: Reflective String String
chars =
  labelled
    [ ("char_", (: []) <$> focus _head char_),
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
letter = labelled (map (\c -> ([c], exact c)) (['a' .. 'z'] ++ ['A' .. 'Z']))

-- unescapedspecial = "/" | "+" | ":" | "@" | "$" | "!" | "'" | "(" | "," | "." | ")" | "-" | "#" | "_" | ... "%" | "=" | ">" | "<" | "{" | "}" | "^" | "*" | "|" | ";" | " " ; -- NOTE: I had to add some things
unescapedspecial :: Reflective Char Char
unescapedspecial = labelled (map (\c -> ([c], exact c)) ['/', '+', ':', '@', '$', '!', '\'', '(', ',', '.', ')', '-', '#', '_'])

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
hexletter = labelled (map (\c -> ([c], exact c)) ['f', 'e', 'F', 'A', 'D', 'a', 'B', 'd', 'E', 'c', 'b', 'C'])

-- number = int_ frac exp | int_ frac | int_ exp | int_ ;
number :: Reflective String String
number =
  labelled
    [ ("int_", int_),
      ("int_ exp", int_ >>- \i -> expo >>- \ex -> pure (i ++ ex)),
      ("int_ frac", int_ >>- \i -> frac >>- \f -> pure (i ++ f)),
      ("int_ frac exp", int_ >>- \i -> frac >>- \f -> expo >>- \ex -> pure (i ++ f ++ ex))
    ]

-- int_ = nonzerodigit digits | "-" digit digits | digit | "-" digit ;
int_ :: Reflective String String
int_ =
  labelled
    [ ("nonzero digits", (:) <$> focus _head nonzerodigit <*> focus _tail digits),
      ("digit", (: []) <$> focus _head digit),
      ( "'-' digit",
        (\x y -> x : [y])
          <$> focus _head (exact '-')
          <*> focus (_tail . _head) digit
      ),
      ("'-' digit digits", (:) <$> focus _head (exact '-') <*> focus _tail ((:) <$> focus _head digit <*> focus _tail digits))
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
  labelled (map (\c -> ([c], exact c)) ['1', '2', '3', '4', '5', '6', '7', '8', '9'])

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
    str = string1
    string1 =
      labelled
        [ ( "'\"' char_ '\"'",
            do
              do
                q1 <- lmap (take 1) (exact ['"'])
                c <- lmap (!! 1) char_
                q2 <- lmap (take 1 . drop 2) (exact ['"'])
                pure (q1 ++ [c] ++ q2)
          ),
          ( "'\"' chars '\"'",
            do
              q1 <- lmap (take 1) (exact ['"'])
              cs <- lmap (drop 1) chars
              q2 <- lmap (take 1 . drop (1 + length cs)) (exact ['"'])
              pure (q1 ++ cs ++ q2)
          )
        ]
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

withChecksum :: Reflective String String
withChecksum = do
  let a = "{\"payload\":"
  let b = ",\"checksum\":"
  let c = "}"
  _ <- lmap (take (length a)) (exact a)
  payload <- lmap (drop (length a)) start
  let checksum = take 8 (show (abs (hash payload)))
  _ <- lmap (take (length b) . drop (length a + length payload)) (exact b)
  _ <- lmap (take (length checksum) . drop (length a + length payload + length b)) (exact checksum)
  _ <- lmap (take (length c) . drop (length a + length payload + length b + length checksum)) (exact c)
  pure (a ++ payload ++ b ++ checksum ++ c)
  where
    hash = foldl' (\h c -> 33 * h `xor` fromEnum c) 5381