-- | This is a shell monad, for generating shell scripts.
--
-- The emphasis is on generating shell code that will work in any POSIX
-- compliant shell and avoids many common shell pitfalls, including
-- insufficient quoting, while allowing the Haskell type checker to be
-- leveraged for additional safety.
--
-- Here is a hello world example.
--
-- > {-# LANGUAGE OverloadedStrings, ExtendedDefaultRules #-}
-- > import Control.Monad.Shell
-- > import Data.Monoid
-- > import qualified Data.Text.Lazy as T
-- > import qualified Data.Text.Lazy.IO as T
-- > default (T.Text)
-- > 
-- > main :: IO ()
-- > main = T.writeFile "hello.sh" $ script $ do
-- > 	cmd "echo" "hello, world"
-- > 	username <- newVarFrom (Output (cmd "whoami")) ()
-- > 	cmd "echo" "from" (WithVar username (<> "'s shell"))
--
-- When run, that generates this shell code:
-- 
-- > #!/bin/sh
-- > echo 'hello, world'
-- > _v="$(whoami)"
-- > echo from "$_v"''"'"'s shell'
--
-- There are several other examples shipped in the examples/ directory
-- of the shell-monad package. For example, protocol.hs shows how 
-- shell-monad can be used to implement a shell script that speaks a
-- protocol that is defined using Haskell data types.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeOperators #-}

module Control.Monad.Shell (
	-- * Core
	Script,
	script,
	linearScript,
	Term,
	Var,
	Static,
	Quoted,
	Quotable(..),
	glob,
	-- * Running commands
	run,
	cmd,
	Param,
	CmdParams,
	Output(..),
	-- * Shell variables
	NamedLike(..),
	NameHinted,
	static,
	newVar,
	newVarFrom,
	newVarContaining,
	setVar,
	globalVar,
	positionalParameters,
	takeParameter,
	defaultVar,
	whenVar,
	lengthVar,
	trimVar,
	Greediness(..),
	Direction(..),
	WithVar(..),
	-- * Monadic combinators
	func,
	forCmd,
	whileCmd,
	ifCmd,
	whenCmd,
	unlessCmd,
	caseOf,
	subshell,
	group,
	withEnv,
	(-|-),
	(-&&-),
	(-||-),
	-- * Redirection
	RedirFile,
	(|>),
	(|$>),
	(|>>),
	(|<),
	toStderr,
	(>&),
	(<&),
	(&),
	hereDocument,
	-- * Error handling
	stopOnFailure,
	pipeFail,
	ignoreFailure,
	errUnlessVar,
	-- * Tests
	test,
	Test(..),
	-- * Shell Arithmetic Expressions
	val,
	Arith(..),
	-- * Misc
	comment,
	readVar,
	readVars,
) where

import qualified Data.Text.Lazy as L
import qualified Data.Set as S
import Data.Char
import System.Posix.Types (Fd)
import System.Posix.IO (stdInput, stdOutput, stdError)

import Control.Monad.Shell.Quote

-- | A term that can be expanded in a shell command line.
data Term t a where
	VarTerm :: UntypedVar -> Term Var a
	StaticTerm :: (Quotable (Val a)) => a -> Term Static a

-- | Used to represent a shell variable.
data Var
-- | Used for a static value.
data Static

data UntypedVar = V
	{ varName :: VarName
	, expandVar :: Env -> VarName -> Quoted L.Text
	}

newtype VarName = VarName L.Text
	deriving (Eq, Ord, Show)

simpleVar :: forall a. VarName -> Term Var a
simpleVar = VarTerm . simpleVar'

simpleVar' :: VarName -> UntypedVar
simpleVar' name = V
	{ varName = name
	-- Used to expand the variable; can be overridden for other
	-- types of variable expansion.
	--
	-- It's important that the shell code this generates never
	-- contain any quotes. That would prevent it from being nested
	-- inside an arithmatic expression.
	, expandVar = \_ (VarName n) -> Q ("$" <> n)
	}

-- | Treats the Text as a glob.
--
-- When used as a 'Param' to a command, it expands to one parameter per
-- matching file.
--
-- > forCmd (cmd "ls" (glob "*/*.cabal")) $ \file ->
-- >     cmd "echo" file
--
-- When used in a 'caseOf', it matches text against the glob.
--
-- The input is assumed to be a well-formed glob. Characters in it that
-- are not alphanumeric and are not wildcard characters will be escaped
-- before it is exposed to the shell. This allows eg, spaces in globs.
glob :: L.Text -> Quoted L.Text
glob = Q . L.concatMap escape
  where
	escape c
		| isAlphaNum c = L.singleton c
		| c `elem` ("*?[!-:]\\" :: String) = L.singleton c
		| otherwise = "\\" <> L.singleton c

-- | A shell function.
newtype Func = Func L.Text
	deriving (Eq, Ord, Show)

class Named t where
	getName :: t -> L.Text

instance Named (Term Var t) where
	getName (VarTerm v) = getName v

instance Named UntypedVar where
	getName = getName . varName

instance Named VarName where
	getName (VarName n) = n

instance Named Func where
	getName (Func n) = n

type Indent = Int

type LocalEnv = (L.Text, L.Text)

-- | A shell expression.
data Expr
	= Cmd Indent [LocalEnv] L.Text
	-- ^ a command. may have a local environment to be added to it
	| Raw Indent L.Text
	-- ^ shell code that is not able to a have a local environment added to it
	| EnvWrap Indent L.Text [LocalEnv] [Expr]
	-- ^ named script with a local environment to add to it
	| Comment L.Text -- ^ a comment
	| Subshell L.Text [Expr] -- ^ expressions run in a sub-shell
	| Group L.Text [Expr] -- ^ expressions run in a group
	| Pipe Expr Expr -- ^ Piping the first Expr to the second Expr
	| And Expr Expr -- ^ &&
	| Or Expr Expr -- ^ ||
	| Redir Expr RedirSpec -- ^ Redirects a file handle of the Expr

-- | Indents an Expr
indent :: Expr -> Expr
indent (Cmd i localenvs t) = Cmd (i + 1) localenvs t
indent (Raw i t) = Raw (i + 1) t
indent (EnvWrap i n localenvs e) = EnvWrap (i + 1) n localenvs (map indent e)
indent (Comment t) = Comment $ "\t" <> t
indent (Subshell i l) = Subshell ("\t" <> i) (map indent l)
indent (Group i l) = Group ("\t" <> i) (map indent l)
indent (Pipe e1 e2) = Pipe (indent e1) (indent e2)
indent (Redir e r) = Redir (indent e) r
indent (And e1 e2) = And (indent e1) (indent e2)
indent (Or e1 e2) = Or (indent e1) (indent e2)

-- | Specifies a redirection.
data RedirSpec
	= RedirToFile Fd FilePath -- ^ redirect the fd to a file
	| RedirToFileFromVar Fd (Quoted L.Text)
	  -- ^ redirect to a file whose path is stored in a given variable
	| RedirToFileAppend Fd FilePath -- ^ append to file
	| RedirFromFile Fd FilePath -- ^ use a file as input
	| RedirOutput Fd Fd -- ^ redirect first fd to the second
	| RedirInput Fd Fd -- ^ same, but for input fd
	| RedirHereDoc L.Text -- ^ use a here document as input

-- | Shell script monad.
newtype Script a = Script (Env -> ([Expr], Env, a))
	deriving (Functor)

instance Applicative Script where
	pure a = Script $ \env -> ([], env, a)
	Script f <*> Script a = Script $ \env0 ->
		let (expr1, env1, f') = f env0
		    (expr2, env2, a') = a env1
		in  (expr1 <> expr2, env2, f' a')

instance Monad Script where
	a >>= b = Script $ \start -> let
		(left, mid, v) = call a start
		(right, end, ret) = call (b v) mid
		in (left ++ right, end, ret)
	  where
		call :: Script f -> Env -> ([Expr], Env, f)
		call (Script f) = f

-- | Environment built up by the shell script monad,
-- so it knows which environment variables and functions are in use.
data Env = Env
	{ envVars :: S.Set VarName
	, envFuncs :: S.Set Func
	}

instance Semigroup Env where
	(<>) a b = Env (envVars a <> envVars b) (envFuncs a <> envFuncs b)

instance Monoid Env where
	mempty = Env mempty mempty

getEnv :: Script Env
getEnv = Script $ \env -> ([], env, env)

modifyEnvVars :: Env -> (S.Set VarName -> S.Set VarName) -> Env
modifyEnvVars env f = env { envVars = f (envVars env) }

modifyEnvFuncs :: Env -> (S.Set Func -> S.Set Func) -> Env
modifyEnvFuncs env f = env { envFuncs = f (envFuncs env) }

-- | Runs the monad and generates a list of Expr
gen :: Script f -> [Expr]
gen = fst . runScript mempty

-- | Runs the monad, and returns a list of Expr and the modified
-- environment.
runScript :: Env -> Script f -> ([Expr], Env)
runScript env (Script f) = (code, env') where (code, env', _) = f env

-- | Runs the passed Script, using the current environment,
-- and returns the list of Expr it generates.
runM :: Script () -> Script [Expr]
runM s = Script $ \env -> 
	let (r, env') = runScript env s
	in ([], env', r)

-- | Generates a shell script, including hashbang,
-- suitable to be written to a file.
script :: Script f -> L.Text
script = flip mappend "\n" . L.intercalate "\n" . 
	("#!/bin/sh":) . map (fmt True) . gen

-- | Formats an Expr to shell  script.
--
-- Can generate either multiline or single line shell script.
fmt :: Bool -> Expr -> L.Text
fmt multiline = go
  where
	fmtlocalenvs = L.intercalate " " . map (\(k, v) -> k <> "=" <> v)

	go (Cmd i [] t) = L.pack (replicate i '\t') <> t
	go (Cmd i localenvs t) = L.pack (replicate i '\t') <> fmtlocalenvs localenvs <> " " <> t
	go (Raw i t) = L.pack (replicate i '\t') <> t
	go (EnvWrap i n localenvs e) =
		let (lp, sep) = if multiline
			then (L.pack (replicate i '\t'), "\n")
			else ("", ";")
		in lp <> n <> "() { : " <> sep
		   <> L.intercalate sep (map (go . indent) e) <> sep
		   <> lp <> "}" <> sep
		   <> lp <> fmtlocalenvs localenvs <> " " <> n
	-- Comments are represented using : for two reasons:
	-- 1. To support single line rendering.
	-- 2. So that it's a valid shell expression; any
	-- Expr, including Comment can be combined with any other.
	-- For example, Pipe Comment Comment.
	go (Comment t) = ": " <> getQ (quote (L.filter (/= '\n') t))
	go (Subshell i []) = i <> "( : )"
	go (Subshell i l) =
		let (wrap, sep) = if multiline then ("\n", "\n") else ("", ";")
		in i <> "(" <> wrap <> L.intercalate sep (map (go . indent) l) <> wrap <> i <> ")"
	go (Group i []) = i <> "{ :; }"
	go (Group i l) =
		let (wrap, sep, end) = if multiline then ("\n", "\n", "") else ("", ";", ";")
		in i <> "{" <> wrap <> L.intercalate sep (map (go . indent) l) <> end <> wrap <> i <> "}"
	go (Pipe e1 e2) = go e1 <> " | " <> go e2
	go (And e1 e2) = go e1 <> " && " <> go e2
	go (Or e1 e2) = go e1 <> " || " <> go e2
	go (Redir e r) = let use t = go e <> " " <> t in case r of
		(RedirToFile fd f) ->
			use $ redirFd fd (Just stdOutput) <> "> " <> L.pack f
		(RedirToFileFromVar fd f) ->
			use $ redirFd fd (Just stdOutput) <> "> " <> getQ f
		(RedirToFileAppend fd f) ->
			use $ redirFd fd (Just stdOutput) <> ">> " <> getQ (quote (L.pack f))
		(RedirFromFile fd f) ->
			use $ redirFd fd (Just stdInput) <> "< " <> getQ (quote (L.pack f))
		(RedirOutput fd1 fd2) ->
			use $ redirFd fd1 (Just stdOutput) <> ">&" <> showFd fd2
		(RedirInput fd1 fd2) ->
			use $ redirFd fd1 (Just stdInput) <> "<&" <> showFd fd2
		(RedirHereDoc t)
			| multiline -> 
				let myEOF = eofMarker t
				in use $ "<<" <> myEOF <> "\n"
					<> t 
					<> "\n" 
					<> myEOF
			-- Here documents cannot be represented in a single
			-- line script. Instead, generate:
			-- (echo l1; echo l2; ...) | cmd
			| otherwise ->
				let heredoc = Subshell L.empty $
					flip map (L.lines t) $ \l -> raw $ 
						"echo " <> getQ (quote l)
				in go (Pipe heredoc e)

-- | Displays a Fd for use in a redirection.
-- 
-- Redirections have a default Fd; for example, ">" defaults to redirecting
-- stdout. In this case, the file descriptor number does not need to be
-- included.
redirFd :: Fd -> Maybe Fd -> L.Text
redirFd fd deffd
	| Just fd == deffd = ""
	| otherwise = showFd fd

showFd :: Fd -> L.Text
showFd = L.pack . show

-- | Finds an approriate marker to end a here document; the marker cannot
-- appear inside the text.
eofMarker :: L.Text -> L.Text
eofMarker t = go (1 :: Integer)
  where
	go n = let marker = "EOF" <> if n == 1 then "" else L.pack (show n)
		in if marker `L.isInfixOf` t
			then go (succ n)
			else marker

-- | Generates a single line of shell code.
linearScript :: Script f -> L.Text
linearScript = toLinearScript . gen

toLinearScript :: [Expr] -> L.Text
toLinearScript = L.intercalate "; " . map (fmt False)

-- | Adds a shell command to the script.
run :: L.Text -> [L.Text] -> Script ()
run c ps = add $ newCmd $ L.intercalate " " (map (getQ . quote) (c:ps))

newCmd :: L.Text -> Expr
newCmd l = Cmd 0 [] l

raw :: L.Text -> Expr
raw l = Raw 0 l

-- | Variadic and polymorphic version of 'run'
--
-- A command can be passed any number of Params.
--
-- > demo = script $ do
-- >   cmd "echo" "hello, world"
-- >   name <- newVar ()
-- >   readVar name
-- >   cmd "echo" "hello" name
--
-- For the most efficient use of 'cmd', add the following boilerplate,
-- which will make string literals in your program default to being Text:
--
-- > {-# LANGUAGE OverloadedStrings, ExtendedDefaultRules #-}
-- > {-# OPTIONS_GHC -fno-warn-type-defaults #-}
-- > import Control.Monad.Shell
-- > import qualified Data.Text.Lazy as L
-- > default (L.Text)
--
-- Note that the command to run is itself a Param, so it can be a Text,
-- or a String, or even a Var or Output. For example, this echos "hi":
--
-- > demo = script $ do
-- >    echovar <- newVarContaining "echo" ()
-- >    cmd echovar "hi"
cmd :: (Param command, CmdParams params) => command -> params
cmd c = cmdAll (toTextParam c) []

-- | A Param is anything that can be used as the parameter of a command.
class Param a where
	toTextParam :: a -> Env -> L.Text

-- | Text arguments are automatically quoted.
instance Param L.Text where
	toTextParam = const . getQ . quote

-- | String arguments are automatically quoted.
instance Param String where
	toTextParam = toTextParam . L.pack

instance Param UntypedVar where
	toTextParam v env = "\"" <> getQ (expandVar v env (varName v)) <> "\""

instance Param (Term Var a) where
	toTextParam (VarTerm v) = toTextParam v

instance (Show a) => Param (Term Static a) where
	toTextParam (StaticTerm a) = toTextParam $ quote $ Val a

-- | Allows modifying the value of a shell variable before it is passed to
-- the command.
instance Param (WithVar a) where
	toTextParam (WithVar v f) = getQ . f . Q . toTextParam v

-- | Quoted Text arguments are passed as-is.
instance Param (Quoted L.Text) where
	toTextParam (Q v) = const v

-- | Allows passing the output of a command as a parameter.
instance Param Output where
	toTextParam (Output s) env =
		let t = toLinearScript $ fst $ runScript env s
		in "\"$(" <> t <> ")\""

-- | Allows passing an Arithmetic Expression as a parameter.
instance Param Arith where
	toTextParam a env =
		let t = fmtArith env a
		in "\"" <> t <> "\""

-- | Allows a function to take any number of Params.
class CmdParams t where
	cmdAll :: (Env -> L.Text) -> [Env -> L.Text] -> t

instance (Param arg, CmdParams result) => CmdParams (arg -> result) where
	cmdAll c acc x = cmdAll c (toTextParam x : acc)

instance (f ~ ()) => CmdParams (Script f) where
	cmdAll c acc = Script $ \env -> 
		let ps = map (\f -> f env) (c : reverse acc)
		in ([newCmd $ L.intercalate " " ps], env, ())

-- | The output of a command, or even a more complicated Script
-- can be passed as a parameter to 'cmd'
--
-- Examples:
--
-- > cmd "echo" "hello there," (Output (cmd "whoami"))
-- > cmd "echo" "root's pwent" (Output (cmd "cat" "/etc/passwd" -|- cmd "grep" "root"))
newtype Output = Output (Script ())

-- | Allows modifying the value of a variable before it is passed to a
-- command. The function is passed a Quoted Text which will expand to the
-- value of the variable, and can modify it, by using eg 'mappend'.
--
-- > cmd "rmdir" (WithVar name ("/home/" <>))
data WithVar a = WithVar (Term Var a) (Quoted L.Text -> Quoted L.Text)

-- | Adds an Expr to the script.
add :: Expr -> Script ()
add expr = Script $ \env -> ([expr], env, ())

-- | Adds a comment that is embedded in the generated shell script.
comment :: L.Text -> Script ()
comment = add . Comment

-- | Suggests that a shell variable or function have its name contain
-- the specified Text.
newtype NamedLike = NamedLike L.Text

-- | Class of values that provide a hint for the name to use for a shell
-- variable or function.
--
-- If you don't want to provide a naming hint, use @()@.
--
-- @
-- v1 <- 'newVar' ()
-- @
--
-- To provide a naming hint, use 'NamedLike'.
--
-- @
-- v1 <- 'newVar' ('NamedLike' \"x\")
-- @
class NameHinted h where
	hinted :: (Maybe L.Text -> a) -> h -> a

instance NameHinted () where
	hinted f _ = f Nothing

instance NameHinted NamedLike where
	hinted f (NamedLike h) = f (Just h)

instance NameHinted (Maybe L.Text) where
	hinted = id

-- | Makes a Static Term from any value that can be shown.
static :: (Quotable (Val t)) => t -> Term Static t
static = StaticTerm

-- | Defines a new shell variable, which starts out not being set.
--
-- Each call to newVar will generate a new, unique variable name.
--
-- The namehint can influence this name, but is modified to ensure
-- uniqueness.
newVar :: (NameHinted namehint) => forall a. namehint -> Script (Term Var a)
newVar = newVarContaining' ""

newVarContaining' :: (NameHinted namehint) => L.Text -> namehint -> Script (Term Var t)
newVarContaining' value = hinted $ \namehint -> do
	v <- newVarUnsafe namehint
	Script $ \env -> ([raw (getName v <> "=" <> value)], env, v)

-- | Creates a new shell variable with an initial value coming from any
-- 'Param'.
--
-- For example,
--
-- > packageName <- newVarFrom
-- >      (Output $
-- >          cmd "grep" "-i" "name\\s*:" (glob "*.cabal") -|-
-- >          cmd "perl" "-pe" "s/^name\\s*:\\s*//i")
-- >      (NamedLike "packageName")
--
-- Use this with 'WithVar' to store to modified value of a variable in a new
-- variable.
--
-- > home <- globalVar "HOME"
-- > cabalDir <- newVarFrom (WithVar home (<> "/.cabal")) ()
-- 
-- Or to capture the output of an arithmetic operation.
--
-- > sum <- newVarFrom (val x `APlus` 1) ()
--
newVarFrom
	:: (NameHinted namehint, Param param)
	=> param -> namehint -> Script (Term Var t)
newVarFrom param namehint = do
	v <- newVarUnsafe namehint
	Script $ \env ->
		([raw (getName v <> "=" <> toTextParam param env)], env, v)

-- | Creates a new shell variable, with an initial value which can
-- be anything that can be shown.
--
-- > s <- newVarContaining "foo bar baz" (NamedLike "s")
-- > i <- newVarContaining (1 :: Int) (NamedLike "i")
newVarContaining :: (NameHinted namehint, Quotable (Val t)) => t -> namehint -> Script (Term Var t)
newVarContaining = newVarContaining' . getQ . quote . Val

-- | Sets the Var to the value of the param. 
setVar :: Param param => forall a. Term Var a -> param -> Script ()
setVar v p = Script $ \env -> 
	([raw (getName v <> "=" <> toTextParam p env)], env, ())

-- | Gets a Var that refers to a global variable, such as PATH
globalVar :: forall a. L.Text -> Script (Term Var a)
globalVar name = Script $ \env ->
	let v = simpleVar (VarName name)
	in ([], modifyEnvVars env (S.insert (VarName (getName v))), v)

-- | This special Var expands to whatever parameters were passed to the
-- shell script.
--
-- Inside a func, it expands to whatever parameters were passed to the
-- func.
--
-- (This is `$@` in shell)
positionalParameters :: forall a. Term Var a
positionalParameters = simpleVar (VarName "@")

-- | Takes the first positional parameter, removing it from
-- positionalParameters and returning a new Var that holds the value of the
-- parameter.
--
-- If there are no more positional parameters, the script will crash
-- with an error.
--
-- For example:
--
-- > removefirstfile = script $ do
-- >   cmd "rm" =<< takeParameter
-- >   cmd "echo" "remaining parameters:" positionalParameters
takeParameter :: (NameHinted namehint) => forall a. namehint -> Script (Term Var a)
takeParameter = hinted $ \namehint -> do
	p <- newVarUnsafe namehint
	Script $ \env -> ([raw (getName p <> "=\"$1\""), raw "shift"], env, p)

-- | Creates a new shell variable, but does not ensure that it's not
-- already set to something. For use when the caller is going to generate
-- some shell script that is guaranteed to clobber any existing value of
-- the variable.
newVarUnsafe :: (NameHinted namehint) => forall a. namehint -> Script (Term Var a)
newVarUnsafe hint = VarTerm <$> newVarUnsafe' hint

newVarUnsafe' :: (NameHinted namehint) => namehint -> Script UntypedVar
newVarUnsafe' = hinted $ \namehint -> Script $ \env ->
	let name = go namehint env (0 :: Integer)
	in ([], modifyEnvVars env (S.insert name), simpleVar' name)
  where
	go namehint env x
		| S.member name (envVars env) =
			go namehint env (succ x)
		| otherwise = name
	  where
		name = VarName $ "_"
			<> genvarname namehint
			<> if x == 0 then "" else L.pack (show (x + 1))
	
	genvarname = maybe "v" (L.filter isAlpha)

-- | Generates a new Var. Expanding this Var will yield the same
-- result as expanding the input Var, unless it is empty, in which case
-- it instead defaults to the expansion of the param.
defaultVar :: (Param param) => forall a. Term Var a -> param -> Script (Term Var a)
defaultVar = funcVar' ":-"

-- | Generates a new Var. If the input Var is empty, then this new Var
-- will likewise expand to the empty string. But if not, the new Var
-- expands to the param.
whenVar :: (Param param) => forall a. Term Var a -> param -> Script (Term Var a)
whenVar = funcVar' ":+"

-- | Generates a new Var. If the input Var is empty then expanding this new
-- Var will cause an error to be thrown, using the param as the error
-- message. If the input Var is not empty, then the new Var expands to the
-- same thing the input Var expands to.
errUnlessVar :: (Param param) => forall a. Term Var a -> param -> Script (Term Var a)
errUnlessVar = funcVar' ":?"

-- | Produces a Var that is a trimmed version of the input Var.
--
-- The Quoted Text is removed from the value of the Var, either
-- from the beginning or from the end.
--
-- If the Quoted Text was produced by 'glob', it could match in
-- multiple ways. You can choose whether to remove the shortest or
-- the longest match.
--
-- The act of trimming a Var is assumed to be able to produce a new
-- Var holding a different data type.
trimVar :: forall a. Greediness -> Direction -> Term Var String -> Quoted L.Text -> Script (Term Var a)
trimVar ShortestMatch FromBeginning = funcVar' "#"
trimVar LongestMatch FromBeginning = funcVar' "##"
trimVar ShortestMatch FromEnd = funcVar' "%"
trimVar LongestMatch FromEnd = funcVar' "%%"

data Greediness = ShortestMatch | LongestMatch

data Direction = FromBeginning | FromEnd

-- | Generates a new Var, which expands to the length of the
-- expansion of the input Var.
--
-- Note that 'lengthVar positionalParameters' expands to the number
-- of positional parameters.
lengthVar :: forall a. Term Var a -> Script (Term Var Integer)
lengthVar v
	| getName v == "@" = return $ simpleVar (VarName "#")
	| otherwise = funcVar v ("#" <>)		

-- To implement a Var -> Var function at the shell level,
-- generate shell code like this:
--
-- func () {
-- 	t="$orig"; echo "${t'}"
-- }
--
-- Where t' = transform t
--
-- The returned Var expands to a call to the function: $(func)
-- Note that it's important this call to the function not contain
-- any quotes, so that it can be used inside an arithmetic expression.
funcVar :: forall a b. Term Var a -> (L.Text -> L.Text) -> Script (Term Var b)
funcVar orig transform = do
	v <- newVarUnsafe' shortname
	f <- mkFunc (VarTerm v)
	return $ VarTerm $ v
		{ expandVar = \env _ -> Q $
			"$(" <> toLinearScript (fst (runScript env f)) <> ")"
		}
  where
	mkFunc :: Term Var () -> Script (Script ())
	mkFunc tmp = func shortname $ do
		setVar tmp orig
		cmd ("echo" :: L.Text) $ Q $
			"\"${" <> transform (getName tmp) <> "}\""
	shortname = NamedLike "v"

funcVar' :: (Param param) => forall a b. L.Text -> Term Var a -> param -> Script (Term Var b)
funcVar' op v p = do
	t <- toTextParam p <$> getEnv
	funcVar v (<> op <> t)

-- | Defines a shell function, and returns an action that can be run to
-- call the function.
--
-- The action is variadic; it can be passed any number of CmdParams.
-- Typically, it will make sense to specify a more concrete type
-- when defining the shell function.
--
-- The shell function will be given a unique name, that is not used by any
-- other shell function. The namehint can be used to influence the contents
-- of the function name, which makes for more readable generated shell
-- code.
--
-- For example:
--
-- > demo = script $ do
-- >    hohoho <- mkHohoho
-- >    hohoho (static 1)
-- >    echo "And I heard him exclaim, ere he rode out of sight ..."
-- >    hohoho (static 3)
-- > 
-- > mkHohoho :: Script (Term Val Int -> Script ())
-- > mkHohoho = func (NamedLike "hohoho") $ do
-- >    num <- takeParameter
-- >    forCmd (cmd "seq" "1" num) $ \_n ->
-- >       cmd "echo" "Ho, ho, ho!" "Merry xmas!"
func
	:: (NameHinted namehint, CmdParams callfunc)
	=> namehint
	-> Script ()
	-> Script callfunc
func h s = flip hinted h $ \namehint -> Script $ \env ->
	let f = go (genfuncname namehint) env (0 :: Integer)
	    env' = modifyEnvFuncs env (S.insert f)
	    (ls, env'') = runScript env' s
	in (definefunc f ls, env'', callfunc f)
  where
	go basename env x
		| S.member f (envFuncs env) = go basename env (succ x)
		| otherwise = f
	  where
		f = Func $ "_"
			<> basename
			<> if x == 0 then "" else L.pack (show (x + 1))
	
	genfuncname = maybe "p" (L.filter isAlpha)

	definefunc (Func f) ls = (raw $ f <> " () { :") : map indent ls ++ [ raw "}" ]

	callfunc (Func f) = cmd f

-- | Runs the command, and separates its output into parts
-- (using the IFS)
--
-- The action is run for each part, passed a Var containing the part.
forCmd :: forall a. Script () -> (Term Var a -> Script ()) -> Script ()
forCmd c a = do
	v <- newVarUnsafe (NamedLike "x")
	s <- toLinearScript <$> runM c
	add $ raw $ "for " <> getName v <> " in $(" <> s <> ")"
	block "do" (a v)
	add $ raw "done"

-- | As long as the first Script exits nonzero, runs the second script.
whileCmd :: Script () -> Script () -> Script ()
whileCmd c a = do
	s <- toLinearScript <$> runM c
	add $ raw $ "while $(" <> s <> ")"
	block "do" a
	add $ raw "done"

-- | if with a Script conditional.
--
-- If the conditional exits 0, the first action is run, else the second.
ifCmd :: Script () -> Script () -> Script () -> Script ()
ifCmd cond thena elsea = 
	ifCmd' id cond $ do
		block "then" thena
		block "else" elsea

ifCmd' :: (L.Text -> L.Text) -> Script () -> Script () -> Script ()
ifCmd' condf cond body = do
	condl <- runM cond
	add $ raw $ "if " <> condf (singleline condl)
	body
	add $ raw "fi"
  where
	singleline l =
		let c = case l of
			[c'@(Cmd {})] -> c'
			[c'@(Raw {})] -> c'
			[c'@(Subshell {})] -> c'
			_ -> Subshell L.empty l
		in toLinearScript [c]

-- | when with a monadic conditional
whenCmd :: Script () -> Script () -> Script ()
whenCmd cond a = 
	ifCmd' id cond $
		block "then" a

-- | unless with a monadic conditional
unlessCmd :: Script () -> Script () -> Script ()
unlessCmd cond a =
	ifCmd' ("! " <>) cond $
		block "then" a

-- | Matches the value of the Var against the Quoted Text (which can
-- be generated by 'glob'), and runs the Script action associated
-- with the first match.
--
-- > arg <- takeParameter ()
-- > caseOf arg
-- >   [ (quote "-h", showHelp)
-- >   , (glob "-*", cmd "echo" "Unknown option:" arg)
-- >   ]
caseOf :: forall a. Term Var a -> [(Quoted L.Text, Script ())] -> Script ()
caseOf _ [] = return ()
caseOf v l = go True l
  where
	-- The case expression is formatted somewhat unusually,
	-- in order to make it work in both single line and multi-line
	-- rendering.
	--
	-- > case "$foo" in ook) : 
	-- >     echo got ook
	-- >     echo yay
	-- > : ;; *) :
	-- >     echo default
	-- > : ;; esac
	go _ [] = add $ raw ";; esac"
	go atstart ((t, s):rest) = do
		env <- getEnv
		let leader = if atstart
			then "case " <> toTextParam v env <> " in "
			else ": ;; "
		add $ raw $ leader <> getQ t <> ") :"
		mapM_ (add . indent) =<< runM s
		go False rest

-- | Runs the script in a new subshell.
subshell :: Script () -> Script ()
subshell s = do
	e <- runM s
	add $ Subshell "" e

-- | Runs the script as a command group in the current subshell.
group :: Script () -> Script ()
group s = do
	e <- runM s
	add $ Group "" e

-- | Add a variable to the local environment of the script.
withEnv :: Param value => L.Text -> value -> Script () -> Script ()
withEnv n v (Script f) = Script $ addEnv . f
  where
	-- We can only add K=V to simple commands. If the input script
	-- contains anything more than one simple command we'll have to wrap
	-- the script into a fresh function and call that with the
	-- environment.
	addEnv (e, env, _) = let localenv = (n, toTextParam v env)
		in case e of
			[Cmd i localenvs l] -> ([Cmd i (localenv : localenvs) l], env, ())
			[EnvWrap i envName localenvs e'] -> ([EnvWrap i envName (localenv : localenvs) e'], env, ())
			l -> ([EnvWrap 0 (getName name) [localenv] l], env', ())
	  where
		(Script nameFn) = newVarUnsafe' (NamedLike "envfn")
		(_, env', name) = nameFn env

-- | Creates a block such as "do : ; cmd ; cmd" or "else : ; cmd ; cmd"
--
-- The use of : ensures that the block is not empty, and allows
-- for more regular indentation, as well as making the single line
-- formatting work.
block :: L.Text -> Script () -> Script ()
block word s = do
	add $ raw $ word <> " :"
	mapM_ (add . indent) =<< runM s

-- | Fills a variable with a line read from stdin.
readVar :: Term Var L.Text -> Script ()
readVar v = readVars [v]

-- | Fill multiple variables by reading their values from stdin.
readVars :: [Term Var L.Text] -> Script ()
readVars [] = error "needs at least one variable to fill"
readVars vs =
	let names = L.intercalate " " [getQ (quote (getName v)) | v <- vs]
	in add $ newCmd $ "read -r " <> names

-- | By default, shell scripts continue running past commands that exit
-- nonzero. Use 'stopOnFailure True' to make the script stop on the first
-- such command.
stopOnFailure :: Bool -> Script ()
stopOnFailure b = add $ raw $ "set " <> (if b then "-" else "+") <> "e"

-- | Control the pipefail option. After calling 'pipeFail True', any failing
-- command will cause the failure of the entire enclosing pipeline.
pipeFail :: Bool -> Script ()
pipeFail b = add $ raw $ "set " <> (if b then "-" else "+") <> "o pipefail"

-- | Makes a nonzero exit status be ignored.
ignoreFailure :: Script () -> Script ()
ignoreFailure s = runM s >>= mapM_ (add . go)
  where
	go c@(Cmd _ _ _) = Or c true
	go c@(Raw _ _) = Or c true
	go c@(Comment _) = c
	go (EnvWrap i n localenvs e) = EnvWrap i n localenvs (map go e)
	go (Subshell i l) = Subshell i (map go l)
	go (Group i l) = Group i (map go l)
	-- Assumes pipefail is not set.
	go (Pipe e1 e2) = Pipe e1 (go e2)
	-- Note that in shell, a && b || true will result in true;
	-- there is no need for extra parens.
	go c@(And _ _) = Or c true
	go (Or e1 e2) = Or e1 (go e2)
	go (Redir e r) = Redir (go e) r

	true = raw "true"

-- | Pipes together two Scripts.
(-|-) :: Script () -> Script () -> Script ()
(-|-) = combine Pipe

-- | ANDs two Scripts.
(-&&-) :: Script () -> Script () -> Script ()
(-&&-) = combine And

-- | ORs two Scripts.
(-||-) :: Script () -> Script () -> Script ()
(-||-) = combine Or

combine :: (Expr -> Expr -> Expr) -> Script () -> Script () -> Script ()
combine f a b = do
	alines <- runM a
	blines <- runM b
	add $ f (toSingleExp alines) (toSingleExp blines)

toSingleExp :: [Expr] -> Expr
toSingleExp [e] = e
toSingleExp l = Subshell L.empty l

redir :: Script () -> (Env -> RedirSpec) -> Script ()
redir s r = do
	e <- toSingleExp <$> runM s
	env <- getEnv
	add $ Redir e (r env)

-- | Any function that takes a RedirFile can be passed a
-- a FilePath, in which case the default file descriptor will be redirected
-- to/from the FilePath.
--
-- Or, it can be passed a tuple of (Fd, FilePath), in which case the
-- specified Fd will be redirected to/from the FilePath.
class RedirFile r where
	fromRedirFile :: Fd -> r -> (Fd, FilePath)

instance RedirFile FilePath where
	fromRedirFile = (,)

instance RedirFile (Fd, FilePath) where
	fromRedirFile = const id

fileRedir :: RedirFile f => f -> Fd -> (Fd -> FilePath -> RedirSpec) -> RedirSpec
fileRedir f deffd c = uncurry c (fromRedirFile deffd f)

-- | Redirects to a file, overwriting any existing file.
--
-- For example, to shut up a noisy command:
--
-- > cmd "find" "/" |> "/dev/null"
(|>) :: RedirFile f => Script () -> f -> Script ()
s |> f = redir s (const $ fileRedir f stdOutput RedirToFile)

(|$>) :: Script () -> Term Var t -> Script ()
s |$> v = redir s (RedirToFileFromVar stdOutput . Q. toTextParam v)

-- | Appends to a file. (If file doesn't exist, it will be created.)
(|>>) :: RedirFile f => Script () -> f -> Script ()
s |>> f = redir s (const $ fileRedir f stdOutput RedirToFileAppend)

-- | Redirects standard input from a file.
(|<) :: RedirFile f => Script () -> f -> Script ()
s |< f = redir s (const $ fileRedir f stdInput RedirFromFile)

-- | Redirects a script's output to stderr.
toStderr :: Script () -> Script ()
toStderr s = s &stdOutput>&stdError

-- | Redirects the first file descriptor to output to the second.
--
-- For example, to redirect a command's stderr to stdout:
--
-- > cmd "foo" &stdError>&stdOutput
(>&) :: (Script (), Fd) -> Fd -> Script ()
(s, fd1) >& fd2 = redir s (const $ RedirOutput fd1 fd2)

-- | Redirects the first file descriptor to input from the second.
--
-- For example, to read from Fd 42:
--
-- > cmd "foo" &stdInput<&Fd 42
(<&) :: (Script (), Fd) -> Fd -> Script ()
(s, fd1) <& fd2 = redir s (const $ RedirInput fd1 fd2)

-- | Helper for '>&' and '<&'
(&) :: Script () -> Fd -> (Script (), Fd)
(&) = (,)

-- | Provides the Text as input to the Script, using a here-document.
hereDocument :: Script () -> L.Text -> Script ()
hereDocument s t = redir s (const $ RedirHereDoc t)

-- | Creates a Script that checks a Test and exits true (0) or false (1).
--
-- Useful with ifCmd, whenCmd, etc; for example:
--
-- > ifCmd (test (FileExists "foo")) (foo, bar)
test :: Test -> Script ()
test t = Script $ \env -> ([newCmd $ "test " <> mkTest env t], env, ())

mkTest :: Env -> Test -> L.Text
mkTest env = go
  where
	go (TNot t) = unop "!" (go t)
	go (TAnd t1 t2) = binop (go t1) "&&" (go t2)
	go (TOr t1 t2) = binop (go t1) "||" (go t2)
	go (TEmpty p) = unop "-z" (pv p)
	go (TNonEmpty p) = unop "-n" (pv p)
	go (TStrEqual p1 p2) = binop (pv p1) "=" (pv p2)
	go (TStrNotEqual p1 p2) = binop (pv p1) "!=" (pv p2)
	go (TEqual p1 p2) = binop (pv p1) "-eq" (pv p2)
	go (TNotEqual p1 p2) = binop (pv p1) "-ne" (pv p2)
	go (TGT p1 p2) = binop (pv p1) "-gt" (pv p2)
	go (TLT p1 p2) = binop (pv p1) "-lt" (pv p2)
	go (TGE p1 p2) = binop (pv p1) "-ge" (pv p2)
	go (TLE p1 p2) = binop (pv p1) "-le" (pv p2)
	go (TFileEqual p1 p2) = binop (pv p1) "-ef" (pv p2)
	go (TFileNewer p1 p2) = binop (pv p1) "-nt" (pv p2)
	go (TFileOlder p1 p2) = binop (pv p1) "-ot" (pv p2)
	go (TBlockExists p) = unop "-b" (pv p)
	go (TCharExists p) = unop "-c" (pv p)
	go (TDirExists p) = unop "-d" (pv p)
	go (TFileExists p) = unop "-e" (pv p)
	go (TRegularFileExists p) = unop "-f" (pv p)
	go (TSymlinkExists p) = unop "-L" (pv p)
	go (TFileNonEmpty p) = unop "-s" (pv p)
	go (TFileExecutable p) = unop "-x" (pv p)

	paren t = "\\( " <> t <> " \\)"
	
	binop a o b = paren $ a <> " " <> o <> " " <> b
	unop o v = paren $ o <> " " <> v

	pv :: (Param p) => p -> L.Text
	pv = flip toTextParam env

-- | Note that this should only include things that test(1) and
-- shell built-in test commands support portably.
data Test where
	TNot :: Test -> Test -- negation
	TAnd :: Test -> Test -> Test -- 'and'
	TOr :: Test -> Test -> Test -- 'or'
	TEmpty :: (Param p) => p -> Test
	-- Does the param expand to an empty string?
	TNonEmpty :: (Param p) => p -> Test
	TStrEqual :: (Param p, Param q) => p -> q -> Test
	-- Do the parameters expand to the same string?
	TStrNotEqual :: (Param p, Param q) => p -> q -> Test
	TEqual :: (Integral p, Integral q) => Term Var p -> Term Var q -> Test
	-- Are the Vars equal? (Compares integer to integer, not string-wise.)
	TNotEqual :: (Integral p, Integral q) => Term Var p -> Term Var q -> Test 
	TGT :: (Integral p, Integral q) => Term Var p -> Term Var q -> Test -- '>'
	TLT :: (Integral p, Integral q) => Term Var p -> Term Var q -> Test -- '<'
	TGE :: (Integral p, Integral q) => Term Var p -> Term Var q -> Test -- '>='
	TLE :: (Integral p, Integral q) => Term Var p -> Term Var q -> Test -- '<='
	TFileEqual :: (Param p, Param q) => p -> q -> Test
	-- Are the files equal? (Compares the files' device and inode numbers).
	TFileNewer :: (Param p, Param q) => p -> q -> Test
	-- Does the first file have a newer modification date?
	TFileOlder :: (Param p, Param q) => p -> q -> Test
	TBlockExists :: (Param p) => p -> Test
	-- Does the block device exist?
	TCharExists :: (Param p) => p -> Test
	-- Does the char device exist?
	TDirExists :: (Param p) => p -> Test
	-- Does the directory exist?
	TFileExists :: (Param p) => p -> Test
	-- Does the file exist?
	TRegularFileExists :: (Param p) => p -> Test
	-- Does the file exist and is it a regular file?
	TSymlinkExists :: (Param p) => p -> Test
	-- Does the symlink exist?
	TFileNonEmpty :: (Param p) => p -> Test
	-- Does the file exist and is not empty?
	TFileExecutable :: (Param p) => p -> Test
	-- Does the file exist and is executable?

instance (Show a, Num a) => Num (Term Static a) where
	fromInteger = static . fromInteger
	(StaticTerm a) + (StaticTerm b) = StaticTerm (a + b)
	(StaticTerm a) * (StaticTerm b) = StaticTerm (a * b)
	(StaticTerm a) - (StaticTerm b) = StaticTerm (a - b)
	abs (StaticTerm a) = StaticTerm (abs a)
	signum (StaticTerm a) = StaticTerm (signum a)

-- | Lifts a Term to Arith.
val :: Term t Integer -> Arith
val t@(VarTerm _) = AVar t
val t@(StaticTerm _) = AStatic t

-- | This data type represents shell Arithmetic Expressions.
--
-- Note that in shell arithmetic, expressions that would evaluate to a
-- Bool, such as ANot and AEqual instead evaluate to 1 for True and 0 for
-- False.
-- 
data Arith
	= ANum Integer
	| AVar (Term Var Integer)
	| AStatic (Term Static Integer)
	| ANegate Arith -- ^ negation
	| APlus Arith Arith -- ^ '+'
	| AMinus Arith Arith -- ^ '-'
	| AMult Arith Arith -- ^ '*'
	| ADiv Arith Arith -- ^ '/'
	| AMod Arith Arith -- ^ 'mod'
	| ANot Arith -- ^ 'not'
	| AOr Arith Arith -- ^ 'or'
	| AAnd Arith Arith -- ^ 'and'
	| AEqual Arith Arith -- ^ '=='
	| ANotEqual Arith Arith -- ^ '/='
	| ALT Arith Arith -- ^ '<'
	| AGT Arith Arith -- ^ '>'
	| ALE Arith Arith -- ^ '<='
	| AGE Arith Arith -- ^ '>='
	| ABitOr Arith Arith -- ^ OR of the bits of the two arguments
	| ABitXOr Arith Arith -- ^ XOR of the bits of the two arguments
	| ABitAnd Arith Arith -- ^ AND of the bits of the two arguments
	| AShiftLeft Arith Arith -- ^ shift left (first argument's bits are shifted by the value of the second argument)
	| AShiftRight Arith Arith -- ^ shift right
	| AIf Arith (Arith, Arith) -- ^ if the first argument is non-zero, the result is the second, else the result is the third

fmtArith :: Env -> Arith -> L.Text
fmtArith env arith = "$(( " <> go arith <> " ))"
  where
	go (ANum i) = L.pack (show i)
	-- shell variable must be expanded without quotes
	go (AVar (VarTerm v)) = getQ $ expandVar v env (varName v)
	go (AStatic (StaticTerm v)) = getQ $ quote $ Val v
	go (ANegate v) = unop "-" v
	go (APlus a b) = binop a "+" b
	go (AMinus a b) = binop a "-" b
	go (AMult a b) = binop a "*" b
	go (ADiv a b) = binop a "/" b
	go (AMod a b) = binop a "%" b
	go (ANot v) = unop "!" v
	go (AOr a b) = binop a "||" b
	go (AAnd a b) = binop a "&&" b
	go (AEqual a b) = binop a "==" b
	go (ANotEqual a b) = binop a "!=" b
	go (ALT a b) = binop a "<" b
	go (AGT a b) = binop a ">" b
	go (ALE a b) = binop a "<=" b
	go (AGE a b) = binop a ">=" b
	go (ABitOr a b) = binop a "|" b
	go (ABitXOr a b) = binop a "^" b
	go (ABitAnd a b) = binop a "&" b
	go (AShiftLeft a b) = binop a "<<" b
	go (AShiftRight a b) = binop a ">>" b
	go (AIf c (a, b)) = paren $ go c <> " ? " <> go a <> " : " <> go b

	paren t = "(" <> t <> ")"

	binop a o b = paren $ go a <> " " <> o <> " " <> go b
	unop o v = paren $ o <> " " <> go v

-- | Arith is an instance of Num, which allows you to write expressions
-- like this with shell variables, that generate Arithmetic Expressions.
--
-- > val x * (100 + val y)
instance Num Arith where
	fromInteger = ANum
	(+) = APlus
	(*) = AMult
	(-) = AMinus
	negate = ANegate
	abs v = AIf (v `ALT` ANum 0)
		( AMult v (ANum (-1))
		, v
		)
	signum v = 
		AIf (v `ALT` ANum 0)
			( ANum (-1)
			, AIf (v `AGT` ANum 0)
				( ANum 1
				, ANum 0
				)
			)

-- | Note that 'fromEnum', 'enumFromTo', and 'enumFromThenTo' cannot be used
-- with Arith.
instance Enum Arith where
	succ a = APlus a (ANum 1)
	pred a = AMinus a (ANum 1)
	toEnum = ANum . fromIntegral
	enumFrom a = a : enumFrom (succ a)
	enumFromThen a b = a : enumFromThen b ((b `AMult` ANum 2) `AMinus` a)
	fromEnum = error "fromEnum not implemented for Arith"
	enumFromTo = error "enumFromTo not implemented for Arith"
	enumFromThenTo = error "enumFromToThen not implemented for Arith"
