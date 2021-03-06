{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Text.HTML.KURE
        ( -- * Reading HTML
          parseHTML,
          -- * HTML Builders
          element,
          text,
          attr,
          zero,
          -- * Primitive Traversal Combinators
          htmlT, htmlC,
          elementT, elementC,
          textT, textC,
          attrsT, attrsC,
          attrT, attrC,
          -- * Other Combinators and Observers
          getAttr,
          isTag,
          getTag,
          getAttrs,
          getInner,
          anyElementHTML,
          unconcatHTML,
          -- * Types and Classes
          HTML,
          Element,
          Text,
          Attrs,
          Attr,
          Syntax,
          Context(..),
          Node,
          Html(..),
          -- * KURE combinators synonyms specialized to our universe type 'Node'
          injectT',
          projectT',
          extractT',
          promoteT',
          extractR',
          promoteR'
       )where

import Text.XML.HXT.Parser.HtmlParsec
import Text.XML.HXT.DOM.ShowXml
import Text.XML.HXT.DOM.TypeDefs
import Text.XML.HXT.DOM.XmlNode
-- import Data.Tree.NTree.TypeDefs
-- import Text.XML.HXT.Parser.XmlParsec hiding (element)
-- import Text.XML.HXT.Parser.XhtmlEntities

import Control.Arrow
import Data.Char
import Data.Monoid (Monoid(..))
import Control.Monad
#if __GLASGOW_HASKELL__ >= 800
import Data.Semigroup (Semigroup(..))
#endif

--import Language.KURE.Walker
import qualified Language.KURE as KURE
import Language.KURE hiding ()

-- | The Principal type in DSL. Use 'show' to get the String rendition of this type.
-- 'HTML' is concatenated using '<>', the 'Monoid' mappend.
newtype HTML  = HTML XmlTrees

-- | HTML element with tag and attrs
newtype Element = Element XmlTree

-- | Text (may include escaped text internally)
newtype Text  = Text XmlTrees   -- precondition: XmlTrees is never []

-- | Attributes for a element
newtype Attrs = Attrs XmlTrees

-- | Single attribute
newtype Attr  = Attr XmlTree

-- | XML/HTML syntax, like <? or <!, or our zero-width space 'zero'.
newtype Syntax  = Syntax XmlTree

-- | Context contains all the containing elements
-- in an inside to outside order
newtype Context = Context [Element]

-- | Our universal node type. Only used during
-- generic tree walking and traversals.
data Node
        = HTMLNode      HTML
        | ElementNode   Element
        | TextNode      Text
        | AttrsNode     Attrs
        | AttrNode      Attr
        | SyntaxNode    Syntax
        deriving Show

-----------------------------------------------------------------------------

instance Show HTML where
        show (HTML html) = xshow html

instance Show Element where
        show (Element html) = xshow [html]

instance Show Text where
        show (Text html) = xshow html

instance Show Attrs where
        show (Attrs html) = xshow html

instance Show Attr where
        show (Attr html) = xshow [html]

instance Show Syntax where
        show (Syntax syntax) = xshow [syntax]

#if __GLASGOW_HASKELL__ >= 800
instance Semigroup HTML where
        (<>) = mappend

instance Semigroup Context where
        (<>) = mappend
#endif

instance Monoid HTML where
        mempty = HTML []
        mappend (HTML xs) (HTML ys) = HTML $ xs ++ ys

instance Monoid Context where
        mempty = Context []
        mappend (Context xs) (Context ys) = Context $ xs ++ ys

-----------------------------------------------------------------------------
-- KURE specific instances

instance Injection HTML Node where
        inject    = HTMLNode
        project u = do HTMLNode t <- return u
                       return t

instance Injection Element Node where
        inject    = ElementNode
        project u = do ElementNode t <- return u
                       return t

instance Injection Text Node where
        inject    = TextNode
        project u = do TextNode t <- return u
                       return t

instance Injection Attrs Node where
        inject    = AttrsNode
        project u = do AttrsNode t <- return u
                       return t

instance Injection Attr Node where
        inject    = AttrNode
        project u = do AttrNode t <- return u
                       return t

instance Injection Syntax Node where
        inject    = SyntaxNode
        project u = do SyntaxNode t <- return u
                       return t

instance Walker Context Node where
        allR :: forall m . MonadCatch m => Rewrite Context m Node -> Rewrite Context m Node
        allR rr = prefixFailMsg "allR failed: " $
          rewrite $ \ c -> \ case
            HTMLNode  o  -> liftM HTMLNode  $ KURE.applyT (htmlT (extractR rr >>> arr html)
                                                                 (extractR rr >>> arr html)
                                                                 (extractR rr >>> arr html)   $ htmlC) c o
            ElementNode o  -> liftM ElementNode  $ KURE.applyT (elementT (extractR rr) (extractR rr) $ elementC) c o
            TextNode  o  -> liftM TextNode   $ return o
            AttrsNode o  -> liftM AttrsNode  $ KURE.applyT (attrsT (extractR rr)               $ attrsC) c o
            AttrNode  o  -> liftM AttrNode   $ return o
            SyntaxNode o -> liftM SyntaxNode $ return o -- never processed

class Html a where
        html :: a -> HTML

instance Html Element where
        html (Element b) = HTML [b]

instance Html Text where
        html (Text b) = HTML b

instance Html Syntax where
        html (Syntax b) = HTML [b]


-----------------------------------------------------------------------------

-- | 'htmlT' take arrows that operate over elements, texts, and syntax,
-- and returns a transformation over HTML.

htmlT :: (Monad m)
     => Transform Context m Element a             -- used many times
     -> Transform Context m Text a              -- used many times
     -> Transform Context m Syntax a            -- used many times
     -> ([a] -> x)
     -> Transform Context m HTML x
htmlT tr1 tr2 tr3 k = transform $ \ c (HTML ts) -> liftM k $ flip mapM ts $ \ case
                        t@(NTree (XTag {}) _)     -> applyT tr1 c (Element t)
                        t@(NTree (XText {}) _)    -> applyT tr2 c (Text [t])
                        t@(NTree (XCharRef {}) _) -> applyT tr2 c (Text [t])
                        t@(NTree (XPi {}) _)      -> applyT tr3 c (Syntax t)
                        t@(NTree (XDTD {}) _)     -> applyT tr3 c (Syntax t)
                        t@(NTree (XCmt {}) _)     -> applyT tr3 c (Syntax t)
                        t@(NTree (XError {}) _)   -> applyT tr3 c (Syntax t)
                        t -> error $ "not XTag or XText: " ++ take 100 (show t)

-- | 'mconcat' over 'HTML'
htmlC :: [HTML] -> HTML
htmlC = mconcat

-- | 'elementT' take arrows that operate over attributes and (the inner) HTML,
-- and returns a transformation over a single element.

elementT :: (Monad m)
     => Transform Context m Attrs a
     -> Transform Context m HTML b
     -> (String -> a -> b -> x)
     -> Transform Context m Element x
elementT tr1 tr2 k = transform $ \ (Context cs) (Element t) ->
        case t of
          NTree (XTag tag attrs) rest
            | namePrefix tag == ""
           && namespaceUri tag == "" -> do
                  let nm = localPart tag
                  let c = Context (Element t : cs)
                  attrs' <- applyT tr1 c (Attrs attrs)
                  rest'  <- applyT tr2 c (HTML rest)
                  return $ k nm attrs' rest'
          _ -> fail "elementT runtime type error"

-- | 'elementC' builds a element from its components.
elementC :: String -> Attrs -> HTML -> Element
elementC nm (Attrs attrs) (HTML rest) = Element (NTree (XTag (mkName nm) attrs) rest)

-- | 'textT' takes a Text to bits. The string is fully unescaped (a regular Haskell string)
textT :: (Monad m)
      => (String -> x)
      -> Transform Context m Text x
textT k = transform $ \ _ (Text txt) ->
          return $ k $ unescapeText $ [ fn t | (NTree t _) <- txt ]
  where
          fn (XText    xs) = Left xs
          fn (XCharRef c)  = Right c
          fn _             = error "found non XText / XCharRef in Text"

-- | 'textC' constructs a Text from a fully unescaped string.
textC :: String -> Text
textC ""  = Text [ NTree (XText "") [] ]
textC str = Text [ NTree t [] | t <-  map (either XText XCharRef) $ escapeText str ]

-- | 'attrsT' promotes a transformation over 'Attr' into a transformation over 'Attrs'.
attrsT :: (Monad m)
       => Transform Context m Attr a
       -> ([a] -> x)
       -> Transform Context m Attrs x
attrsT tr k = transform $ \ c (Attrs ts) -> liftM k $ flip mapM ts $ \ case
                        t@(NTree (XAttr {}) _) -> applyT tr c (Attr t)
                        _                      -> fail "not XTag or XText"

-- | join attributes together.
attrsC :: [Attr] -> Attrs
attrsC xs = Attrs [ x | Attr x <- xs ]


-- | promote a function over an attributes components into a transformation over 'Attr'.
attrT :: (Monad m)
      => (String -> String -> x)
      -> Transform Context m Attr x
attrT k = transform $ \ c -> \ case
                Attr (NTree (XAttr nm) ts)
                   | namePrefix nm == ""
                  && namespaceUri nm == "" -> applyT (textT $ k (localPart nm)) c (Text ts)
                _                          -> fail "textT runtime error"

-- | Create a single attribute.
attrC :: String -> String -> Attr
attrC nm val = Attr $ mkAttr (mkName nm) ts
  where Text ts = textC val

--------------------------------------------------
-- HTML Builders.

-- | 'element' is the main way of generates a element in HTML.
element :: String -> [Attr] -> HTML -> HTML
element nm xs inner = HTML [t]
  where Element t = elementC nm (attrsC xs) inner

-- | 'text' creates a HTML node with text inside it.
text :: String -> HTML
text txt = HTML ts
  where Text ts = textC txt

-- | 'zero' is an empty piece of HTML, which can be used to avoid
-- the use of the \<tag/\> form; for example "element \"br\" [] zero" will generate both an opener and closer.
-- 'zero' is the same as "text \"\"".
zero :: HTML
zero = text ""

----------------------------------------------------
-- Attr builder

-- | build a single Attr. Short version of 'attrC'.
attr :: String -> String -> Attr
attr = attrC

--------------------------------------------------
-- Element observers

-- | 'getAttr' gets the attributes of a specific attribute of a element.
getAttr :: (MonadCatch m) => String -> Transform Context m Element String
getAttr nm = getAttrs >>> attrsT find catchesM >>> joinT
  where
          find :: (MonadCatch m) => Transform Context m Attr (m String)
          find = attrT $ \ nm' val -> if nm' == nm
                                      then return val
                                      else fail $ "getAttr: not" ++ show nm

-- | 'isTag' checks the element for a specific element name.
isTag :: (Monad m) => String -> Transform Context m Element ()
isTag nm = elementT idR idR (\ nm' _ _ -> nm == nm') >>> guardT

-- | 'getTag' gets the element name.
getTag :: (Monad m) => Transform Context m Element String
getTag = elementT idR idR (\ nm _ _ -> nm)

-- | 'getAttrs' gets the attributes inside a element.
getAttrs :: (Monad m) => Transform Context m Element Attrs
getAttrs = elementT idR idR (\ _ as _ -> as)

-- | 'getInner' gets the HTML inside a element.
getInner :: (Monad m) => Transform Context m Element HTML
getInner = elementT idR idR (\ _ _ h -> h)

--------------------------------------------------
-- common pattern; promote a transformation over a element to over

injectT' :: (Monad m, Injection a Node) => Transform c m a Node
injectT' = injectT

projectT' :: (Monad m, Injection a Node) => Transform c m Node a
projectT' = projectT

extractT' :: (Monad m, Injection a Node) => Transform c m Node b -> Transform c m a b
extractT' = extractT

promoteT' :: (Monad m, Injection a Node) => Transform c m a b -> Transform c m Node b
promoteT' = promoteT

extractR' :: (Monad m, Injection a Node) => Rewrite c m Node -> Rewrite c m a
extractR' = extractR

promoteR' :: (Monad m, Injection a Node) => Rewrite c m a -> Rewrite c m Node
promoteR' = promoteR

---------------------------------------

-- | Flatten into singleton HTMLs. The opposite of mconcat.
unconcatHTML :: HTML -> [HTML]
unconcatHTML (HTML ts) = map (\ t -> HTML [t]) ts

-- | lifts mapping of 'Element' to 'HTML' over a single level of 'HTML' sub-nodes.
-- 'anyElementHTML' has the property ''anyElementHTML (arr html) = idR''.
--
-- This is successful only if any of the sub-transformations are successful.
anyElementHTML :: (MonadCatch m) => Transform Context m Element HTML -> Rewrite Context m HTML
anyElementHTML tr = arr unconcatHTML >>> unwrapAnyR (mapT (wrapAnyR $ extractT' $ oneT $ promoteT' tr)) >>> arr mconcat

-- | parsing HTML files. If you want to unparse, use 'show'.
parseHTML :: FilePath -> String -> HTML
parseHTML fileName input = HTML $ parseHtmlDocument fileName input

---------------------------------------

escapeText :: String -> [Either String Int]
escapeText = foldr join [] . map f
  where f n | n == '<'  = Right (ord n)
            | n == '"'  = Right (ord n)
            | n == '&'  = Right (ord n)
            | n == '\n' = Left n
            | n == '\t' = Left n
            | n == '\r' = Left n
            | n > '~'   = Right (ord n)
            | n < ' '   = Right (ord n)
            | otherwise = Left n
        join (Left x) (Left xs :rest) = Left (x : xs) : rest
        join (Left x) rest            = Left [x] : rest
        join (Right x) rest           = Right x : rest

unescapeText :: [Either String Int] -> String
unescapeText = concatMap (either id ((: []) . chr))







