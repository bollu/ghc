{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Pretty
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  David Terei <code@davidterei.com>
-- Stability   :  stable
-- Portability :  portable
--
-- John Hughes's and Simon Peyton Jones's Pretty Printer Combinators
--
-- Based on /The Design of a Pretty-printing Library/
-- in Advanced Functional Programming,
-- Johan Jeuring and Erik Meijer (eds), LNCS 925
-- <http://www.cs.chalmers.se/~rjmh/Papers/pretty.ps>
--
-----------------------------------------------------------------------------

{-
Note [Differences between libraries/pretty and compiler/utils/Pretty.hs]

For historical reasons, there are two different copies of `Pretty` in the GHC
source tree:
 * `libraries/pretty` is a submodule containing
   https://github.com/haskell/pretty. This is the `pretty` library as released
   on hackage. It is used by several other libraries in the GHC source tree
   (e.g. template-haskell and Cabal).
 * `compiler/utils/Pretty.hs` (this module). It is used by GHC only.

There is an ongoing effort in https://github.com/haskell/pretty/issues/1 and
https://ghc.haskell.org/trac/ghc/ticket/10735 to try to get rid of GHC's copy
of Pretty.

Currently, GHC's copy of Pretty resembles pretty-1.1.2.0, with the following
major differences:
 * GHC's copy uses `Faststring` for performance reasons.
 * GHC's copy has received a backported bugfix for #12227, which was
   released as pretty-1.1.3.4 ("Remove harmful $! forcing in beside",
   https://github.com/haskell/pretty/pull/35).

Other differences are minor. Both copies define some extra functions and
instances not defined in the other copy. To see all differences, do this in a
ghc git tree:

    $ cd libraries/pretty
    $ git checkout v1.1.2.0
    $ cd -
    $ vimdiff compiler/utils/Pretty.hs \
              libraries/pretty/src/Text/PrettyPrint/HughesPJ.hs

For parity with `pretty-1.1.2.1`, the following two `pretty` commits would
have to be backported:
  * "Resolve foldr-strictness stack overflow bug"
    (307b8173f41cd776eae8f547267df6d72bff2d68)
  * "Special-case reduce for horiz/vert"
    (c57c7a9dfc49617ba8d6e4fcdb019a3f29f1044c)
This has not been done sofar, because these commits seem to cause more
allocation in the compiler (see thomie's comments in
https://github.com/haskell/pretty/pull/9).
-}

module Pretty  (

        -- * The document type
        Doc,

        -- * Constructing documents

        -- ** Converting values into documents
        char, text, ftext, ptext, ztext, sizedText, zeroWidthText,
        int, integer, float, double, rational,

        -- ** Simple derived documents
        semi, comma, colon, space, equals,
        lparen, rparen, lbrack, rbrack, lbrace, rbrace,

        -- ** Wrapping documents in delimiters
        parens, brackets, braces, quotes, quote, doubleQuotes,
        maybeParens,

        -- ** Combining documents
        empty,
        (<>), (<+>), hcat, hsep,
        ($$), ($+$), vcat,
        sep, cat,
        fsep, fcat,
        nest,
        Pretty.hang, hangNotEmpty, punctuate,

        -- * Predicates on documents
        isEmpty,

        -- * Rendering documents

        -- ** Rendering with a particular style
        Style(..),
        style,
        renderStyle,
        Mode(..),

        -- ** General rendering
        -- fullRender,

        -- ** GHC-specific rendering
        printDoc, printDoc_,
        -- bufLeftRender -- performance hack

  ) where

import BufWrite
import FastString
import Panic
import System.IO
import Prelude hiding (error)

--for a RULES
import GHC.Base ( unpackCString# )
import GHC.Ptr  ( Ptr(..) )

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL


import Data.Text.Prettyprint.Doc
-- PI = PrettyprinterInternal
import Data.Text.Prettyprint.Doc.Internal as PI

import Data.Text.Prettyprint.Doc.Render.Text

import  GHC.Float (float2Double)


-- Don't import Util( assertPanic ) because it makes a loop in the module structure


-- ---------------------------------------------------------------------------
-- The Doc calculus

{-
Laws for $$
~~~~~~~~~~~
<a1>    (x $$ y) $$ z   = x $$ (y $$ z)
<a2>    empty $$ x      = x
<a3>    x $$ empty      = x

        ...ditto $+$...

Laws for <>
~~~~~~~~~~~
<b1>    (x <> y) <> z   = x <> (y <> z)
<b2>    empty <> x      = empty
<b3>    x <> empty      = x

        ...ditto <+>...

Laws for text
~~~~~~~~~~~~~
<t1>    text s <> text t        = text (s++t)
<t2>    text "" <> x            = x, if x non-empty

** because of law n6, t2 only holds if x doesn't
** start with `nest'.


Laws for nest
~~~~~~~~~~~~~
<n1>    nest 0 x                = x
<n2>    nest k (nest k' x)      = nest (k+k') x
<n3>    nest k (x <> y)         = nest k x <> nest k y
<n4>    nest k (x $$ y)         = nest k x $$ nest k y
<n5>    nest k empty            = empty
<n6>    x <> nest k y           = x <> y, if x non-empty

** Note the side condition on <n6>!  It is this that
** makes it OK for empty to be a left unit for <>.

Miscellaneous
~~~~~~~~~~~~~
<m1>    (text s <> x) $$ y = text s <> ((text "" <> x) $$
                                         nest (-length s) y)

<m2>    (x $$ y) <> z = x $$ (y <> z)
        if y non-empty


Laws for list versions
~~~~~~~~~~~~~~~~~~~~~~
<l1>    sep (ps++[empty]++qs)   = sep (ps ++ qs)
        ...ditto hsep, hcat, vcat, fill...

<l2>    nest k (sep ps) = sep (map (nest k) ps)
        ...ditto hsep, hcat, vcat, fill...

Laws for oneLiner
~~~~~~~~~~~~~~~~~
<o1>    oneLiner (nest k p) = nest k (oneLiner p)
<o2>    oneLiner (x <> y)   = oneLiner x <> oneLiner y

You might think that the following verion of <m1> would
be neater:

<3 NO>  (text s <> x) $$ y = text s <> ((empty <> x)) $$
                                         nest (-length s) y)

But it doesn't work, for if x=empty, we would have

        text s $$ y = text s <> (empty $$ nest (-length s) y)
                    = text s <> nest (-length s) y
-}

-- ---------------------------------------------------------------------------
-- Operator fixity
{-
infixl 6 <>
infixl 6 <+>
infixl 5 $$, $+$
-}
($+$) :: Doc a -> Doc a -> Doc a
($+$) a b = vsep [a, b]

($$) :: Doc a -> Doc a -> Doc a
($$) = ($+$)



char :: Char -> Doc a
char = pretty


-- | A document of height 1 containing a literal string.
-- 'text' satisfies the following laws:
--
-- * @'text' s '<>' 'text' t = 'text' (s'++'t)@
--
-- * @'text' \"\" '<>' x = x@, if @x@ non-empty
--
-- The side condition on the last law is necessary because @'text' \"\"@
-- has height 1, while 'empty' has no height.

text :: String -> Doc a
text = pretty

-- DEPRECATED
{-# DEPRECATED zeroWidthText "woo" #-}
zeroWidthText :: String -> Doc a
zeroWidthText s = PI.Text 0 (T.pack s)


ftext :: FastString -> Doc a
ftext = pretty . unpackFS

ptext :: LitString -> Doc a
ptext = pretty . unpackLitString

ztext :: FastZString -> Doc a
ztext = pretty . zString

-- | Some text with any width. (@text s = sizedText (length s) s@)
sizedText :: Int -> String -> Doc a
sizedText size s = PI.Text size (T.pack s)

int      :: Int      -> Doc a -- ^ @int n = text (show n)@
integer  :: Integer  -> Doc a -- ^ @integer n = text (show n)@
float    :: Float    -> Doc a -- ^ @float n = text (show n)@
double   :: Double   -> Doc a -- ^ @double n = text (show n)@
rational :: Rational -> Doc a -- ^ @rational n = text (show n)@
int       = pretty
integer   = pretty
float     = pretty
double    = pretty
rational  = pretty . show

lbrack :: Doc a -- ^ A '[' character
lbrack = lbracket

rbrack :: Doc a -- ^ A ']' character
rbrack = rbracket

quotes       :: Doc a -> Doc a -- ^ Wrap document in @\'...\'@
quotes = squotes

doubleQuotes :: Doc a -> Doc a -- ^ Wrap document in @\"...\"@
doubleQuotes = dquotes

quote     :: Doc a -> Doc a-- ^Prefix document with @\'@
quote p        = char '\'' <> p


-- | Apply 'parens' to 'Doc' if boolean is true.
maybeParens :: Bool -> Doc a -> Doc a
maybeParens False = id
maybeParens True = parens

empty :: Doc a
empty = emptyDoc

-- | \"Paragraph fill\" version of 'sep'.
fsep :: [Doc a] -> Doc a
fsep = sep

fcat :: [Doc a] -> Doc a
fcat = cat

-- | Returns 'True' if the document is empty
isEmpty :: Doc a -> Bool
isEmpty PI.Empty = True
isEmpty _     = False

-- | @hang d1 n d2 = sep [d1, nest n d2]@
hang :: Doc a -> Int -> Doc a -> Doc a
hang d1 n d2 = sep [d1, nest n d2]



-- | Apply 'hang' to the arguments if the first 'Doc' is not empty.
hangNotEmpty :: Doc a -> Int -> Doc a -> Doc a
hangNotEmpty d1 n d2 = if isEmpty d1
                       then d2
                       else Pretty.hang d1 n d2

-- ---------------------------------------------------------------------------
-- Rendering


-- | A rendering style.
data Style
  = Style { mode           :: Mode  -- ^ The rendering mode
          , lineLength     :: Int   -- ^ Length of line, in chars
          , ribbonsPerLine :: Float -- ^ Ratio of line length to ribbon length
          }

-- | The default style (@mode=PageMode, lineLength=100, ribbonsPerLine=1.5@).
style :: Style
style = Style { lineLength = 100, ribbonsPerLine = 1.5, mode = PageMode }

-- | Rendering mode.
data Mode = PageMode     -- ^ Normal
          | ZigZagMode   -- ^ With zig-zag cuts
          | LeftMode     -- ^ No indentation, infinitely long lines
          | OneLineMode  -- ^ All on one line

-- currently ignoring Mode. Need to respect this later on
styleToLayoutOptions :: Style -> LayoutOptions
styleToLayoutOptions s = case (mode s) of
                          LeftMode -> LayoutOptions Unbounded
                          _ -> LayoutOptions (AvailablePerLine (lineLength s) (float2Double (ribbonsPerLine s)))

-- | Render the @Doc@ to a String using the given @Style@.
renderStyle :: Style -> Doc a -> String
renderStyle s d = TL.unpack $ renderLazy (layoutPretty (styleToLayoutOptions s) d)

printDoc :: Mode -> Int -> Handle -> Doc a -> IO ()
-- printDoc adds a newline to the end
printDoc mode cols hdl doc = printDoc_ mode cols hdl (doc <> line)

printDoc_ :: Mode -> Int -> Handle -> Doc a -> IO ()
printDoc_ mode pprCols hdl doc = 
  TL.hPutStr hdl (renderLazy (layoutPretty (mkLayoutOptions mode pprCols) doc)) where
  mkLayoutOptions :: Mode -> Int -> LayoutOptions
  -- Note that this should technically be 1.5 as per the old implementation.
  -- I have no idea why that is.
  mkLayoutOptions PageMode pprCols = LayoutOptions (AvailablePerLine pprCols 1.0)
  mkLayoutOptions LeftMode pprCols = LayoutOptions Unbounded


-- printDoc_ does not add a newline at the end, so that
-- successive calls can output stuff on the same line
-- Rather like putStr vs putStrLn
-- printDoc_ LeftMode _ hdl doc
--   = do { printLeftRender hdl doc; hFlush hdl }
-- printDoc_ mode pprCols hdl doc
--   = do { fullRender mode pprCols 1.5 put done doc ;
--          hFlush hdl }
--   where
--     put (Chr c)  next = hPutChar hdl c >> next
--     put (Str s)  next = hPutStr  hdl s >> next
--     put (PStr s) next = hPutStr  hdl (unpackFS s) >> next
--                         -- NB. not hPutFS, we want this to go through
--                         -- the I/O library's encoding layer. (#3398)
--     put (ZStr s) next = hPutFZS  hdl s >> next
--     put (LStr s l) next = hPutLitString hdl s l >> next

--     done = return () -- hPutChar hdl '\n'


{-
-- | Default TextDetails printer
txtPrinter :: TextDetails -> String -> String
txtPrinter (Chr c)   s  = c:s
txtPrinter (Str s1)  s2 = s1 ++ s2
txtPrinter (PStr s1) s2 = unpackFS s1 ++ s2
txtPrinter (ZStr s1) s2 = zString s1 ++ s2
txtPrinter (LStr s1 _) s2 = unpackLitString s1 ++ s2

-- | The general rendering interface.
fullRender :: Mode                     -- ^ Rendering mode
           -> Int                      -- ^ Line length
           -> Float                    -- ^ Ribbons per line
           -> (TextDetails -> a -> a)  -- ^ What to do with text
           -> a                        -- ^ What to do at the end
           -> Doc                      -- ^ The document
           -> a                        -- ^ Result
fullRender OneLineMode _ _ txt end doc
  = easyDisplay spaceText (\_ y -> y) txt end (reduceDoc doc)
fullRender LeftMode    _ _ txt end doc
  = easyDisplay nlText first txt end (reduceDoc doc)

fullRender m lineLen ribbons txt rest doc
  = display m lineLen ribbonLen txt rest doc'
  where
    doc' = best bestLineLen ribbonLen (reduceDoc doc)

    bestLineLen, ribbonLen :: Int
    ribbonLen   = round (fromIntegral lineLen / ribbons)
    bestLineLen = case m of
                      ZigZagMode -> maxBound
                      _          -> lineLen
easyDisplay :: TextDetails
             -> (Doc -> Doc -> Doc)
             -> (TextDetails -> a -> a)
             -> a
             -> Doc
             -> a
easyDisplay nlSpaceText choose txt end
  = lay
  where
    lay NoDoc              = error "easyDisplay: NoDoc"
    lay (Union p q)        = lay (choose p q)
    lay (Nest _ p)         = lay p
    lay Empty              = end
    lay (NilAbove p)       = nlSpaceText `txt` lay p
    lay (TextBeside s _ p) = s `txt` lay p
    lay (Above {})         = error "easyDisplay Above"
    lay (Beside {})        = error "easyDisplay Beside"

display :: Mode -> Int -> Int -> (TextDetails -> a -> a) -> a -> Doc -> a
display m !page_width !ribbon_width txt end doc
  = case page_width - ribbon_width of { gap_width ->
    case gap_width `quot` 2 of { shift ->
    let
        lay k _            | k `seq` False = undefined
        lay k (Nest k1 p)  = lay (k + k1) p
        lay _ Empty        = end
        lay k (NilAbove p) = nlText `txt` lay k p
        lay k (TextBeside s sl p)
            = case m of
                    ZigZagMode |  k >= gap_width
                               -> nlText `txt` (
                                  Str (replicate shift '/') `txt` (
                                  nlText `txt`
                                  lay1 (k - shift) s sl p ))

                               |  k < 0
                               -> nlText `txt` (
                                  Str (replicate shift '\\') `txt` (
                                  nlText `txt`
                                  lay1 (k + shift) s sl p ))

                    _ -> lay1 k s sl p
        lay _ (Above {})   = error "display lay Above"
        lay _ (Beside {})  = error "display lay Beside"
        lay _ NoDoc        = error "display lay NoDoc"
        lay _ (Union {})   = error "display lay Union"

        lay1 !k s !sl p    = let !r = k + sl
                             in indent k (s `txt` lay2 r p)

        lay2 k _ | k `seq` False   = undefined
        lay2 k (NilAbove p)        = nlText `txt` lay k p
        lay2 k (TextBeside s sl p) = s `txt` lay2 (k + sl) p
        lay2 k (Nest _ p)          = lay2 k p
        lay2 _ Empty               = end
        lay2 _ (Above {})          = error "display lay2 Above"
        lay2 _ (Beside {})         = error "display lay2 Beside"
        lay2 _ NoDoc               = error "display lay2 NoDoc"
        lay2 _ (Union {})          = error "display lay2 Union"

        -- optimise long indentations using LitString chunks of 8 spaces
        indent !n r | n >= 8    = LStr (sLit "        ") 8 `txt`
                                  indent (n - 8) r
                    | otherwise = Str (spaces n) `txt` r
    in
    lay 0 doc
    }}

printDoc :: Mode -> Int -> Handle -> Doc -> IO ()
-- printDoc adds a newline to the end
printDoc mode cols hdl doc = printDoc_ mode cols hdl (doc $$ text "")

printDoc_ :: Mode -> Int -> Handle -> Doc -> IO ()
-- printDoc_ does not add a newline at the end, so that
-- successive calls can output stuff on the same line
-- Rather like putStr vs putStrLn
printDoc_ LeftMode _ hdl doc
  = do { printLeftRender hdl doc; hFlush hdl }
printDoc_ mode pprCols hdl doc
  = do { fullRender mode pprCols 1.5 put done doc ;
         hFlush hdl }
  where
    put (Chr c)  next = hPutChar hdl c >> next
    put (Str s)  next = hPutStr  hdl s >> next
    put (PStr s) next = hPutStr  hdl (unpackFS s) >> next
                        -- NB. not hPutFS, we want this to go through
                        -- the I/O library's encoding layer. (#3398)
    put (ZStr s) next = hPutFZS  hdl s >> next
    put (LStr s l) next = hPutLitString hdl s l >> next

    done = return () -- hPutChar hdl '\n'

  -- some versions of hPutBuf will barf if the length is zero
hPutLitString :: Handle -> Ptr a -> Int -> IO ()
hPutLitString handle a l = if l == 0
                            then return ()
                            else hPutBuf handle a l

-- Printing output in LeftMode is performance critical: it's used when
-- dumping C and assembly output, so we allow ourselves a few dirty
-- hacks:
--
-- (1) we specialise fullRender for LeftMode with IO output.
--
-- (2) we add a layer of buffering on top of Handles.  Handles
--     don't perform well with lots of hPutChars, which is mostly
--     what we're doing here, because Handles have to be thread-safe
--     and async exception-safe.  We only have a single thread and don't
--     care about exceptions, so we add a layer of fast buffering
--     over the Handle interface.

printLeftRender :: Handle -> Doc -> IO ()
printLeftRender hdl doc = do
  b <- newBufHandle hdl
  bufLeftRender b doc
  bFlush b

bufLeftRender :: BufHandle -> Doc -> IO ()
bufLeftRender b doc = layLeft b (reduceDoc doc)

layLeft :: BufHandle -> Doc -> IO ()
layLeft b _ | b `seq` False  = undefined -- make it strict in b
layLeft _ NoDoc              = error "layLeft: NoDoc"
layLeft b (Union p q)        = layLeft b (first p q)
layLeft b (Nest _ p)         = layLeft b p
layLeft b Empty              = bPutChar b '\n'
layLeft b (NilAbove p)       = bPutChar b '\n' >> layLeft b p
layLeft b (TextBeside s _ p) = put b s >> layLeft b p
 where
    put b _ | b `seq` False = undefined
    put b (Chr c)    = bPutChar b c
    put b (Str s)    = bPutStr  b s
    put b (PStr s)   = bPutFS   b s
    put b (ZStr s)   = bPutFZS  b s
    put b (LStr s l) = bPutLitString b s l
layLeft _ _                  = panic "layLeft: Unhandled case"

-- Define error=panic, for easier comparison with libraries/pretty.
error :: String -> a
error = panic
-}
