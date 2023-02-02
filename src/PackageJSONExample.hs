module PackageJSONExample where

import Control.Lens (_head, _tail)
import Freer

token :: Char -> Reflective b ()
token s = labelled [(['\'', s, '\''], pure ())]

label :: String -> Reflective b ()
label s = labelled [(s, pure ())]

{-# INLINE (>>-) #-}
(>>-) :: Reflective String String -> (String -> Reflective String String) -> Reflective String String
p >>- f = do
  x <- p
  lmap (drop (length x)) (f x)

-- object = "{" "}" | "{" members "}" ;
object :: Reflective String String -> Reflective String String
object val =
  labelled
    [ ("'{' '}'", lmap (take 2) (exact "{}")),
      ( "'{' members '}'",
        lmap (take 1) (exact "{") >>- \b1 ->
          members val >>- \ms ->
            lmap (take 1) (exact "}") >>- \b2 ->
              pure (b1 ++ ms ++ b2)
      )
    ]

-- members = pair | pair ',' members ;
members :: Reflective String String -> Reflective String String
members val =
  labelled
    [ ("pair", pair val),
      ( "pair ',' members",
        pair val >>- \p ->
          lmap (take 1) (exact ",") >>- \c ->
            members val >>- \ps ->
              pure (p ++ c ++ ps)
      )
    ]

-- pair = string ':' value ;
pair :: Reflective String String -> Reflective String String
pair val =
  string >>- \s ->
    lmap (take 1) (exact ":") >>- \c ->
      val >>- \v ->
        pure (s ++ c ++ v)

object' :: [(String, Reflective String String)] -> Reflective String String
object' ps =
  lmap (take 1) (exact "{") >>- \b1 ->
    members' ps >>- \ms ->
      lmap (take 1) (exact "}") >>- \b2 ->
        pure (b1 ++ ms ++ b2)

-- members = pair | pair ',' members ;
members' :: [(String, Reflective String String)] -> Reflective String String
members' [] = pure ""
members' [p] = pair' p
members' (p_ : ps_) =
  pair' p_ >>- \p ->
    lmap (take 1) (exact ",") >>- \c ->
      members' ps_ >>- \ps ->
        pure (p ++ c ++ ps)

-- pair = string ':' value ;
pair' :: (String, Reflective String String) -> Reflective String String
pair' (s, val) =
  lmap (take 1) (exact "\"") >>- \q1 ->
    lmap (take (length s)) (exact s) >>- \_ ->
      lmap (take 1) (exact "\"") >>- \q2 ->
        lmap (take 1) (exact ":") >>- \c ->
          val >>- \v ->
            pure (q1 ++ s ++ q2 ++ c ++ v)

-- array = "[" elements "]" | "[" "]" ;
array :: Reflective String String -> Reflective String String
array val =
  labelled
    [ ("'[' ']'", lmap (take 2) (exact "[]")),
      ( "'[' elements ']'",
        lmap (take 1) (exact "[") >>- \b1 ->
          elements val >>- \ms ->
            lmap (take 1) (exact "]") >>- \b2 ->
              pure (b1 ++ ms ++ b2)
      )
    ]

-- elements = value ',' elements | value ;
elements :: Reflective String String -> Reflective String String
elements val =
  labelled
    [ ("value", val),
      ( "value ',' elements",
        val >>- \el ->
          lmap (take 1) (exact ",") >>- \c ->
            elements val >>- \es ->
              pure (el ++ c ++ es)
      )
    ]

-- value = "f" "a" "l" "s" "e" | string | array | "t" "r" "u" "e" | number | object | "n" "u" "l" "l" ;
value :: Reflective String String
value =
  labelled
    [ ("false", lmap (take 5) (exact "false")),
      ("string", string),
      ("array", array value),
      ("number", number),
      ("true", lmap (take 4) (exact "true")),
      ("object", object value),
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

string1 :: Reflective String String
string1 =
  labelled
    [ ( "'\"' chars '\"'",
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
      ("unescapedspecial", unescapedspecial),
      ("escapedspecial", escapedspecial)
    ]

-- letter = "y" | "c" | "K" | "T" | "s" | "N" | "b" | "S" | "R" | "Y" | "C" | "B" | "h" | "J" | "u" | "Q" | "d" | "k" | "t" | "V" | "a" | "x" | "G" | "v" | "D" | "m" | "F" | "w" | "i" | "n" | "L" | "p" | "q" | "W" | "A" | "X" | "I" | "O" | "l" | "P" | "H" | "e" | "f" | "o" | "j" | "Z" | "g" | "E" | "r" | "M" | "z" | "U" ;
letter :: Reflective Char Char
letter = labelled (map (\c -> ([c], exact c)) (['a' .. 'z'] ++ ['A' .. 'Z']))

-- unescapedspecial = "/" | "+" | ":" | "@" | "$" | "!" | "'" | "(" | "," | "." | ")" | "-" | "#" | "_"
unescapedspecial :: Reflective Char Char
unescapedspecial = labelled (map (\c -> ([c], exact c)) ['/', '+', ':', '@', '$', '!', '\'', '(', ',', '.', ')', '-', '#', '_', ' ', '^'])

-- escapedspecial = "\\b" | "\\n" | "\\r" | "\\/" | "\\u" hextwobyte | "\\\\" | "\\t" | "\\\"" | "\\f" ;
escapedspecial :: Reflective Char Char
escapedspecial =
  labelled
    [ ("'\\b'", exact '\b'),
      ("'\\n'", exact '\n'),
      ("'\\r'", exact '\r'),
      ("'\\/'", exact '/'),
      ("'\\\\'", exact '\\'),
      ("'\\t'", exact '\t'),
      ("'\\f'", exact '\f')
    ]

-- NOTE: Skipped unicode handling to simplify implementation
-- -- hextwobyte = hexdigit hexdigit hexdigit hexdigit ;
-- hextwobyte :: Reflective Char Char
-- hextwobyte = comap (\c -> if c == '\"' then Nothing else Just c) $ do
--   a <- lmap ((!! 0) . printf "%04X" . ord) hexdigit
--   b <- lmap ((!! 1) . printf "%04X" . ord) hexdigit
--   c <- lmap ((!! 2) . printf "%04X" . ord) hexdigit
--   d <- lmap ((!! 3) . printf "%04X" . ord) hexdigit <* token ';'
--   pure (chr (16 * 16 * 16 * digitToInt a + 16 * 16 * digitToInt b + 16 * digitToInt c + digitToInt d))

-- -- hexdigit = hexletter | digit ;
-- hexdigit :: Reflective Char Char
-- hexdigit = labelled [("hexletter", hexletter), ("digit", digit)]

-- -- hexletter = "f" | "e" | "F" | "A" | "D" | "a" | "B" | "d" | "E" | "c" | "b" | "C" ;
-- hexletter :: Reflective Char Char
-- hexletter = labelled (map (\c -> ([c], exact c)) ['f', 'e', 'F', 'A', 'D', 'a', 'B', 'd', 'E', 'c', 'b', 'C'])

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
expo =
  label "e digits"
    >> ( e >>- \e' ->
           digits >>- \d ->
             pure (e' ++ d)
       )

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
  object'
    [ ("name", string1),
      ("description", string1),
      ( "scripts",
        object'
          [ ("start", string1),
            ("build", string1),
            ("test", string1)
          ]
      ),
      ( "repository",
        object'
          [ ("type", string1),
            ("url", string1)
          ]
      ),
      ("keywords", array string),
      ("author", string1),
      ("license", string1),
      ("devDependencies", object string1),
      ("dependencies", object string1)
    ]