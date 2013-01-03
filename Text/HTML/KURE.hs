{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, LambdaCase, InstanceSigs, FlexibleContexts, TypeFamilies #-}

module Text.HTML.KURE
        ( -- * Reading HTML
          parseHTML,
          -- * HTML Builders
          block,
          text,
          -- * Primitive Traversal Combinators
          htmlT, htmlC,
          blockT, blockC,
          textT, textC,
          attrsT, attrsC,
          attrT, attrC,
          -- * Other Combinators and Observers
          getAttr,
          isTag,
          getTag,
          getAttrs,
          getInner,
          concatMapHTML,
          -- * Types and Classes
          HTML,
          Block,
          Text,
          Attrs,
          Attr,
          Syntax,
          Context(..),
          Node,
          Html(..),
          -- * KURE combinators synonyms specialized to our generic type 'Node'
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
import Data.Tree.NTree.TypeDefs
import Text.XML.HXT.Parser.XmlParsec
import Text.XML.HXT.Parser.XhtmlEntities

import Control.Arrow
import Control.Applicative
import Data.Char
import Data.Monoid
import Data.Maybe
import Control.Monad

--import Language.KURE.Walker
import qualified Language.KURE as KURE
import Language.KURE hiding ()

-- | The Principal type in DSL. Use 'show' to get the String rendition of this type.
-- 'HTML' is concatenated using '<>', the 'Monoid' mappend.
newtype HTML  = HTML XmlTrees

-- | HTML block with tag and attrs
newtype Block = Block XmlTree

-- | Text (may include escaped text internally)
newtype Text  = Text XmlTrees

-- | Attributes for a block
newtype Attrs = Attrs XmlTrees

-- | Single attribute
newtype Attr  = Attr XmlTree

-- | XML/HTML syntax, like <? or <!
newtype Syntax  = Syntax XmlTree

-- | Context contains all the containing nodes
-- in an inside to outside order
newtype Context = Context [Block]

-- | Our universal node type. Only used during
-- generic tree walking and traversals.
data Node
        = HTMLNode      HTML
        | BlockNode     Block
        | TextNode      Text
        | AttrsNode     Attrs
        | AttrNode      Attr
        | SyntaxNode    Syntax
        deriving Show

-----------------------------------------------------------------------------

instance Show HTML where
        show (HTML html) = xshow html

instance Show Block where
        show (Block html) = xshow [html]

instance Show Text where
        show (Text html) = xshow html

instance Show Attrs where
        show (Attrs html) = xshow html

instance Show Attr where
        show (Attr html) = xshow [html]

instance Show Syntax where
        show (Syntax syntax) = xshow [syntax]

instance Monoid HTML where
        mempty = HTML []
        mappend (HTML xs) (HTML ys) = HTML $ xs ++ ys

-----------------------------------------------------------------------------
-- KURE specific instances

instance Injection HTML Node where
        inject    = HTMLNode
        project u = do HTMLNode t <- return u
                       return t

instance Injection Block Node where
        inject    = BlockNode
        project u = do BlockNode t <- return u
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
            HTMLNode  o  -> liftM HTMLNode  $ KURE.apply (htmlT  (extractR rr >>> arr html)
                                                                 (extractR rr >>> arr html)
                                                                 (extractR rr >>> arr html)   $ htmlC) c o
            BlockNode o  -> liftM BlockNode  $ KURE.apply (blockT (extractR rr) (extractR rr) $ blockC) c o
            TextNode  o  -> liftM TextNode   $ return o
            AttrsNode o  -> liftM AttrsNode  $ KURE.apply (attrsT (extractR rr)               $ attrsC) c o
            AttrNode  o  -> liftM AttrNode   $ return o
            SyntaxNode o -> liftM SyntaxNode $ return o -- never processed

class Html a where
        html :: a -> HTML

instance Html Block where
        html (Block b) = HTML [b]

instance Html Text where
        html (Text b) = HTML b

instance Html Syntax where
        html (Syntax b) = HTML [b]


-----------------------------------------------------------------------------

-- | 'htmlT' take arrows that operate over blocks, texts, and syntax,
-- and returns a translate over HTML.

htmlT :: (Monad m)
     => Translate Context m Block a             -- used many times
     -> Translate Context m Text a              -- used many times
     -> Translate Context m Syntax a            -- used many times
     -> ([a] -> x)
     -> Translate Context m HTML x
htmlT tr1 tr2 tr3 k = translate $ \ c (HTML ts) -> liftM k $ flip mapM ts $ \ case
                        t@(NTree (XTag {}) _)     -> apply tr1 c (Block t)
                        t@(NTree (XText {}) _)    -> apply tr2 c (Text [t])
                        t@(NTree (XCharRef n) _)  -> apply tr2 c (Text [t])
                        t@(NTree (XPi {}) _)      -> apply tr3 c (Syntax t)
                        t@(NTree (XDTD {}) _)     -> apply tr3 c (Syntax t)
                        t@(NTree (XCmt {}) _)     -> apply tr3 c (Syntax t)
                        t@(NTree (XError {}) _)   -> apply tr3 c (Syntax t)
                        t -> error $ "not XTag or XText: " ++ take 100 (show t)

-- | 'mconcat' over 'HTML'
htmlC :: [HTML] -> HTML
htmlC = mconcat

-- | 'blockT' take arrows that operate over attributes and (the inner) HTML,
-- and returns a translate over a single block.

blockT :: (Monad m)
     => Translate Context m Attrs a
     -> Translate Context m HTML b
     -> (String -> a -> b -> x)
     -> Translate Context m Block x
blockT tr1 tr2 k = translate $ \ (Context cs) (Block t) ->
        case t of
          NTree (XTag tag attrs) rest
            | namePrefix tag == ""
           && namespaceUri tag == "" -> do
                  let nm = localPart tag
                  let c = Context (Block t : cs)
                  attrs' <- apply tr1 c (Attrs attrs)
                  rest'  <- apply tr2 c (HTML rest)
                  return $ k nm attrs' rest'
          _ -> fail "blockT runtime type error"

-- | 'blockC' builds a block from its components.
blockC :: String -> Attrs -> HTML -> Block
blockC nm (Attrs attrs) (HTML rest) = Block (NTree (XTag (mkName nm) attrs) rest)

-- | 'textT' takes a Text to bits. The string is fully unescaped (a regular Haskell string)
textT :: (Monad m)
      => (String -> x)
      -> Translate Context m Text x
textT k = translate $ \ _ (Text txt) ->
          return $ k $ unescapeText $ [ fn t | (NTree t _) <- txt ]
  where
          fn (XText    xs) = Left xs
          fn (XCharRef c)  = Right c
          fn _             = error "found non XText / XCharRef in Text"

--                Text (NTree (XText txt) []) -> return $ k txt
--                Text t@(NTree (XCharRef n) []) -> return $ k $ xshow [t]


-- | 'textC' constructs a Text from a fully unescaped string.
textC :: String -> Text
textC str = Text [ NTree t [] | t <-  map (either XText XCharRef) $ escapeText str ]

-- | 'attrsT' promotes a translation over 'Attr' into a translation over 'Attrs'.
attrsT :: (Monad m)
       => Translate Context m Attr a
       -> ([a] -> x)
       -> Translate Context m Attrs x
attrsT tr k = translate $ \ c (Attrs ts) -> liftM k $ flip mapM ts $ \ case
                        t@(NTree (XAttr {}) _) -> apply tr c (Attr t)
                        _                      -> fail "not XTag or XText"

-- | join attributes together.
attrsC :: [Attr] -> Attrs
attrsC xs = Attrs [ x | Attr x <- xs ]


-- | promote a function over an attributes components into a translate over 'Attr'.
attrT :: (Monad m)
      => (String -> String -> x)
      -> Translate Context m Attr x
attrT k = translate $ \ c -> \ case
                Attr (NTree (XAttr nm) [NTree (XText txt) []])
                   | namePrefix nm == ""
                  && namespaceUri nm == "" -> return $ k (localPart nm) txt
                _                          -> fail "textT runtime error"

-- | Create a single attribute.
attrC :: String -> String -> Attr
attrC nm val = Attr $ mkAttr (mkName nm) [mkText val]


--------------------------------------------------
-- HTML Builders.

-- | 'block' is the main way of generates a block in HTML.
block :: String -> [Attr] -> HTML -> HTML
block nm xs inner = HTML [t]
  where Block t = blockC nm (attrsC xs) inner

-- | 'text' creates a HTML node with text inside it.
text txt = HTML t
  where Text t = textC txt

--------------------------------------------------
-- Block observers

-- | 'getAttr' gets the attributes of a specific attribute of a block.
getAttr :: (MonadCatch m) => String -> Translate Context m Block String
getAttr nm = getAttrs >>> attrsT find catchesM >>> joinT
  where
          find :: (MonadCatch m) => Translate Context m Attr (m String)
          find = attrT $ \ nm' val -> if nm' == nm
                                      then return val
                                      else fail $ "getAttr: not" ++ show nm

-- | 'isTag' checks the block for a specific block name.
isTag :: (Monad m) => String -> Translate Context m Block ()
isTag nm = blockT idR idR (\ nm' _ _ -> nm == nm') >>> guardT

-- | 'getTag' gets the block name.
getTag :: (Monad m) => Translate Context m Block String
getTag = blockT idR idR (\ nm _ _ -> nm)

-- | 'getAttrs' gets the attributes inside a block.
getAttrs :: (Monad m) => Translate Context m Block Attrs
getAttrs = blockT idR idR (\ _ as _ -> as)

-- | 'getInner' gets the HTML inside a block.
getInner :: (Monad m) => Translate Context m Block HTML
getInner = blockT idR idR (\ _ _ h -> h)

--------------------------------------------------
-- common pattern; promote a translation over a block to over

injectT' :: (Monad m, Injection a g, g ~ Node) => Translate c m a g
injectT' = injectT

projectT' :: (Monad m, Injection a g, g ~ Node) => Translate c m g a
projectT' = projectT

extractT' :: (Monad m, Injection a g, g ~ Node) => Translate c m g b -> Translate c m a b
extractT' = extractT

promoteT' :: (Monad m, Injection a g, g ~ Node) => Translate c m a b -> Translate c m g b
promoteT' = promoteT

extractR' :: (Monad m, Injection a g, g ~ Node) => Rewrite c m g -> Rewrite c m a
extractR' = extractR

promoteR' :: (Monad m, Injection a g, g ~ Node) => Rewrite c m a -> Rewrite c m g
promoteR' = promoteR

---------------------------------------

-- | lifts mapping of 'Block' to 'HTML' over a single level of 'HTML' sub-nodes.
-- 'concatMapHTML' has the property ''concatMapHTML (arr html) = idR''.

concatMapHTML :: (Monad m) => Translate Context m Block HTML -> Translate Context m HTML HTML
concatMapHTML tr = htmlT tr (arr html) (arr html) htmlC

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







