-- | This is a shell monad, for generating shell scripts.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Monad.Shell (
	-- * Core
	Script,
	script,
	linearScript,
	Var,
	Val(..),
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
	newVar,
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
	(-|-),
	(-&&-),
	(-||-),
	-- * Redirection
	RedirFile,
	(|>),
	(|>>),
	(|<),
	toStderr,
	(>&),
	(<&),
	(&),
	hereDocument,
	-- * Error handling
	stopOnFailure,
	ignoreFailure,
	errUnlessVar,
	-- * Shell Arithmetic Expressions
	Arith(..),
	-- * Misc
	comment,
	readVar,
) where

import qualified Data.Text.Lazy as L
import qualified Data.Set as S
import Data.Monoid
import Control.Applicative
import Data.Char
import System.Posix.Types (Fd)
import System.Posix.IO (stdInput, stdOutput, stdError)

import Control.Monad.Shell.Quote

-- | A shell variable, with an associated phantom type.
newtype Var a = Var UntypedVar

data UntypedVar = V
	{ varName :: VarName
	, expandVar :: Env -> VarName -> Quoted L.Text
	}

-- | Casts from any type of Var to any other type. Use with caution!
castVar :: forall a b. Var a -> Var b
castVar (Var v) = Var v

newtype VarName = VarName L.Text
	deriving (Eq, Ord, Show)

simpleVar :: forall a. VarName -> Var a
simpleVar name = Var $ V
	{ varName = name
	-- Used to expand the variable; can be overridden for other
	-- types of variable expansion.
	, expandVar = \_ (VarName n) -> Q ("$" <> n)
	}

-- | Treats the Text as a glob, which expands to one parameter per
-- matching file.
--
-- The input is assumed to be a well-formed glob. Characters in it that
-- are not alphanumeric and are not wildcard characters will be escaped
-- before it is exposed to the shell. This allows eg, spaces in globs.
glob :: L.Text -> Quoted L.Text
glob = Q . L.concatMap escape
  where
	escape c
		| isAlphaNum c = L.singleton c
		| c `elem` "*?[!-:]\\" = L.singleton c
		| otherwise = "\\" <> L.singleton c

-- | A shell function.
newtype Func = Func L.Text
	deriving (Eq, Ord, Show)

-- | A shell expression.
data Expr
	= Cmd L.Text -- ^ a command
	| Comment L.Text -- ^ a comment
	| Subshell L.Text [Expr] -- ^ expressions run in a sub-shell
	| Pipe Expr Expr -- ^ Piping the first Expr to the second Expr
	| And Expr Expr -- ^ &&
	| Or Expr Expr -- ^ ||
	| Redir Expr RedirSpec -- ^ Redirects a file handle of the Expr

-- | Indents an Expr
indent :: Expr -> Expr
indent (Cmd t) = Cmd $ "\t" <> t
indent (Comment t) = Comment $ "\t" <> t
indent (Subshell i l) = Subshell ("\t" <> i) (map indent l)
indent (Pipe e1 e2) = Pipe (indent e1) (indent e2)
indent (Redir e r) = Redir (indent e) r
indent (And e1 e2) = And (indent e1) (indent e2)
indent (Or e1 e2) = Or (indent e1) (indent e2)

-- | Specifies a redirection.
data RedirSpec
	= RedirToFile Fd FilePath -- ^ redirect the fd to a file
	| RedirToFileAppend Fd FilePath -- ^ append to file
	| RedirFromFile Fd FilePath -- ^ use a file as input
	| RedirOutput Fd Fd -- ^ redirect first fd to the second
	| RedirInput Fd Fd -- ^ same, but for input fd
	| RedirHereDoc L.Text -- ^ use a here document as input

-- | Shell script monad.
newtype Script a = Script (Env -> ([Expr], Env, a))
	deriving (Functor)

instance Monad Script where
        return ret = Script $ \env -> ([], env, ret)
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

instance Monoid Env where
	mempty = Env mempty mempty
	mappend a b = Env (envVars a <> envVars b) (envFuncs a <> envFuncs b)

modifyEnvVars :: Env -> (S.Set VarName -> S.Set VarName) -> Env
modifyEnvVars env f = env { envVars = f (envVars env) }

modifyEnvFuncs :: Env -> (S.Set Func -> S.Set Func) -> Env
modifyEnvFuncs env f = env { envFuncs = f (envFuncs env) }

-- | runScriptuate the monad and generates a list of Expr
gen :: Script f -> [Expr]
gen = fst . runScript mempty

-- | Runs  the monad, and returns a list of Expr and the modified
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
  where

-- | Formats an Expr to shell  script.
--
-- Can generate either multiline or single line shell script.
fmt :: Bool -> Expr -> L.Text
fmt multiline = go
  where
	go (Cmd t) = t
	go (Comment t)
		| multiline = "# " <> L.filter (/= '\n') t
		-- Comments go to end of line, so instead
		-- use : as a no-op command, and pass the comment to it.
		| otherwise = ": " <> getQ (quote (L.filter (/= '\n') t))
	go (Subshell i l) =
		let (wrap, sep) = if multiline then ("\n", "\n") else ("", ";")
		in i <> "(" <> wrap <> L.intercalate sep (map (go . indent) l) <> wrap <> i <> ")"
	go (Pipe e1 e2) = go e1 <> " | " <> go e2
	go (And e1 e2) = go e1 <> " && " <> go e2
	go (Or e1 e2) = go e1 <> " || " <> go e2
	go (Redir e r) = let use = (\t -> go e <> " " <> t) in case r of
		(RedirToFile fd f) ->
			use $ redirFd fd (Just stdOutput) <> "> " <> L.pack f
		(RedirToFileAppend fd f) ->
			use $ redirFd fd (Just stdOutput) <> ">> " <> L.pack f
		(RedirFromFile fd f) ->
			use $ redirFd fd (Just stdInput) <> "< " <> L.pack f
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
					flip map (L.lines t) $ \l -> Cmd $ 
						"echo " <> getQ (quote l)
				in go (Pipe heredoc e)

-- | Displays a Fd for use in a redirection.
-- 
-- Redirections have a default Fd; for example, ">" defaults to redirecting
-- stdout. In this case, the file descriptor number does not need to be
-- included.
redirFd :: Fd -> (Maybe Fd) -> L.Text
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
run c ps = add $ Cmd $ L.intercalate " " (map (getQ . quote) (c:ps))

-- | Variadic and polymorphic version of 'run'
--
-- A command can be passed any number of Params.
--
-- > demo = script $ do
-- >   cmd "echo" "hello, world"
-- >   name <- newVar "name"
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
	toTextParam :: a -> (Env -> L.Text)

-- | Text arguments are automatically quoted.
instance Param L.Text where
	toTextParam = const . getQ . quote

-- | String arguments are automatically quoted.
instance Param String where
	toTextParam = toTextParam . L.pack

-- | Any value that can be shown can be passed to 'cmd'; just wrap it
-- inside a Val.
instance (Show v) => Param (Val v) where
       toTextParam (Val v) = const $ L.pack (show v)

instance Param UntypedVar where
	toTextParam v = \env -> "\"" <> getQ (expandVar v env (varName v)) <> "\""

-- | Var arguments cause the (quoted) value of a shell variable to be
-- passed to the command.
instance Param (Var a) where
	toTextParam (Var v) = toTextParam v

-- | Allows modifying the value of a shell variable before it is passed to
-- the command.
instance Param (WithVar a) where
	toTextParam (WithVar v f) = getQ . f . Q . toTextParam v

-- | Quoted Text arguments are passed as-is.
instance Param (Quoted L.Text) where
	toTextParam (Q v) = const v

-- | Allows passing the output of a command as a parameter.
instance Param Output where
	toTextParam (Output s) = \env ->
		let t = toLinearScript $ fst $ runScript env s
		in "\"$(" <> t <> ")\""

-- | Allows passing an Arithmetic Expression as a parameter.
instance Param Arith where
	toTextParam a = \env -> 
		let t = fmtArith env a
		in "\"$((" <> t <> "))\""

-- | Allows a function to take any number of Params.
class CmdParams t where
	cmdAll :: (Env -> L.Text) -> [Env -> L.Text] -> t

instance (Param arg, CmdParams result) => CmdParams (arg -> result) where
	cmdAll c acc x = cmdAll c (toTextParam x : acc)

instance (f ~ ()) => CmdParams (Script f) where
	cmdAll c acc = Script $ \env -> 
		let ps = map (\f -> f env) (c : reverse acc)
		in ([Cmd $ L.intercalate " " ps], env, ())

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
data WithVar a = WithVar (Var a) (Quoted L.Text -> Quoted L.Text)

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
-- To skip providing a hint, use '()'.
-- To provide a hint, use '(NamedLike \"name\")'.
class NameHinted h where
	hinted :: (Maybe L.Text -> a) -> h -> a

instance NameHinted () where
	hinted f _ = f Nothing

instance NameHinted NamedLike where
	hinted f (NamedLike h) = f (Just h)

instance NameHinted (Maybe L.Text) where
	hinted = id

-- | Defines a new shell variable, which starts out not being set.
--
-- Each call to newVar will generate a new, unique variable name.
--
-- The namehint can influence this name, but is modified to ensure
-- uniqueness.
newVar :: (NameHinted namehint) => forall a. namehint -> Script (Var a)
newVar = newVarContaining' ""

newVarContaining' :: (NameHinted namehint) => L.Text -> namehint -> Script (Var t)
newVarContaining' value = hinted $ \namehint -> do
	v@(Var (V { varName = VarName name }))
		<- newVarUnsafe namehint
	Script $ \env -> ([Cmd (name <> "=" <> value)], env, v)

-- | Createa a new shell variable, with an initial value which can
-- be anything that can be shown.
--
-- > s <- newVarContaining "foo bar baz" (NamedLike "s")
-- > i <- newVarContaining (1 :: Int) (NamedLine "i")
newVarContaining :: (NameHinted namehint, Quotable (Val t)) => t -> namehint -> Script (Var t)
newVarContaining = newVarContaining' . getQ . quote . Val

-- | Sets the Var to the value of the param. 
setVar :: Param param => forall a. Var a -> param -> Script ()
setVar (Var (V { varName = VarName name })) p = Script $ \env -> 
	([Cmd (name <> "=" <> toTextParam p env)], env, ())

-- | Gets a Var that refers to a global variable, such as PATH
globalVar :: forall a. L.Text -> Script (Var a)
globalVar name = Script $ \env ->
	let v@(Var v') = simpleVar (VarName name)
	in ([], modifyEnvVars env (S.insert (varName v')), v)

-- | This special Var expands to whatever parameters were passed to the
-- shell script.
--
-- Inside a func, it expands to whatever parameters were passed to the
-- func.
--
-- (This is `$@` in shell)
positionalParameters :: forall a. Var a
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
takeParameter :: (NameHinted namehint) => forall a. namehint -> Script (Var a)
takeParameter = hinted $ \namehint -> do
	p@(Var (V { varName = VarName name}))
		<- newVarUnsafe namehint
	Script $ \env -> ([Cmd (name <> "=\"$1\""), Cmd "shift"], env, p)


-- | Creates a new shell variable, but does not ensure that it's not
-- already set to something. For use when the caller is going to generate
-- some shell script that is guaranteed to clobber any existing value of
-- the variable.
newVarUnsafe :: (NameHinted namehint) => forall a. namehint -> Script (Var a)
newVarUnsafe = hinted $ \namehint -> Script $ \env ->
	let v@(Var v') = go namehint env (0 :: Integer)
	in ([], modifyEnvVars env (S.insert (varName v')), v)
  where
	go namehint env x
		| S.member (varName v') (envVars env) =
			go namehint env (succ x)
		| otherwise = v
	  where
		v@(Var v') = simpleVar $ VarName $ "_"
			<> genvarname namehint
			<> if x == 0 then "" else L.pack (show (x + 1))
	
	genvarname = maybe "v" (L.filter isAlpha)

modVar :: forall a b. Var a -> (L.Text -> Env -> L.Text) -> Script (Var b)
modVar (Var (V { varName = VarName varname })) p = do
	(Var v) <- newVarUnsafe (NamedLike varname)
	return $ Var $ v
		{ expandVar = \env _ -> Q $ "${" <> p varname env <> "}"
		}

modVar' :: (Param param) => forall a b. L.Text -> Var a -> param -> Script (Var b)
modVar' t v p = castVar <$> go
   where
	go = modVar v $ \varname env ->
		varname <> t <> toTextParam p env

-- | Generates a new Var. Expanding this Var will yield the same
-- result as expanding the input Var, unless it is empty, in which case
-- it instead defaults to the expansion of the param.
defaultVar :: (Param param) => forall a. Var a -> param -> Script (Var a)
defaultVar = modVar' ":-"

-- | Generates a new Var. If the input Var is empty, then this new Var
-- will likewise expand to the empty string. But if not, the new Var
-- expands to the param.
whenVar :: (Param param) => forall a. Var a -> param -> Script (Var a)
whenVar = modVar' ":+"

-- | Generates a new Var. If the input Var is empty then expanding this new
-- Var will cause an error to be thrown, using the param as the error
-- message. If the input Var is not empty, then the new Var expands to the
-- same thing the input Var expands to.
errUnlessVar :: (Param param) => forall a. Var a -> param -> Script (Var a)
errUnlessVar = modVar' ":?"

-- | Generates a new Var, which expands to the length of the
-- expansion of the input Var.
--
-- Note that 'lengthVar positionalParameters' expands to the number
-- of positional parameters.
lengthVar :: forall a. Var a -> Script (Var Int)
-- Implementation note: ${#${foo:-bar}} is not legal shell code.
-- So, to allow taking the length of Vars that expand to such things,
-- a temporary Var is created, assigned to the expansion of the input Var.
-- This yields shell code like:
-- ${_tmp1:-$(_tmp1="${foo:-bar}"; echo ${#_tmp1})}
-- But, this approach won't work for $@, so handle it as a special
-- case.
lengthVar v@(Var (V { varName = VarName varname }))
	| varname /= "@" = do
		tmpvar@(Var tmpvar') <- newVar (NamedLike "tmp")
		modVar tmpvar $ \tmpname env ->
			let hack = do
				setVar tmpvar v
				cmd ("echo" :: L.Text) $ Var $ tmpvar'
					{ expandVar = \_ _ -> Q $
						"${#" <> tmpname <> "}"
					}
			in varname <> ":-" <> toTextParam (Output hack) env
	| otherwise = return $ simpleVar (VarName "#")

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
trimVar :: forall a. Greediness -> Direction -> Var String -> Quoted L.Text -> Script (Var a)
trimVar ShortestMatch FromBeginning = modVar' "#"
trimVar LongestMatch FromBeginning = modVar' "##"
trimVar ShortestMatch FromEnd = modVar' "%"
trimVar LongestMatch FromEnd = modVar' "%%"

data Greediness = ShortestMatch | LongestMatch

data Direction = FromBeginning | FromEnd

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
-- >    hohoho (Val 1)
-- >    echo "And I heard him exclaim, ere he rode out of sight ..."
-- >    hohoho (Val 3)
-- > 
-- > mkHohoho :: Script (Val Int -> Script ())
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

	definefunc (Func f) ls = (Cmd $ f <> " () { :") : map indent ls ++ [ Cmd "}" ]

	callfunc (Func f) = cmd f

-- | Runs the command, and separates its output into parts
-- (using the IFS)
--
-- The action is run for each part, passed a Var containing the part.
forCmd :: forall a. Script () -> (Var a -> Script ()) -> Script ()
forCmd c a = do
	v@(Var (V { varName = VarName varname})) <- newVarUnsafe (NamedLike "x")
	s <- toLinearScript <$> runM c
	add $ Cmd $ "for " <> varname <> " in $(" <> s <> ")"
	block "do" (a v)
	add $ Cmd "done"

-- | As long as the first Script exits nonzero, runs the second script.
whileCmd :: Script () -> Script () -> Script ()
whileCmd c a = do
	s <- toLinearScript <$> runM c
	add $ Cmd $ "while $(" <> s <> ")"
	block "do" a
	add $ Cmd "done"

-- | if with a monadic conditional
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
	add $ Cmd $ "if " <> condf (singleline condl)
	body
	add $ Cmd "fi"
  where
	singleline l =
		let c = case l of
			[c'@(Cmd {})] -> c'
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
caseOf :: forall a. Var a -> [(Quoted L.Text, Script ())] -> Script ()
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
	go _ [] = add $ Cmd $ ";; esac"
	go atstart ((t, s):rest) = do
		let leader = if atstart
			then "case " <> toTextParam v undefined <> " in "
			else ": ;; "
		add $ Cmd $ leader <> getQ t <> ") :"
		mapM_ (add . indent) =<< runM s
		go False rest

-- | Creates a block such as "do : ; cmd ; cmd" or "else : ; cmd ; cmd"
--
-- The use of : ensures that the block is not empty, and allows
-- for more regular indetnetion, as well as making the single line
-- formatting work.
block :: L.Text -> Script () -> Script ()
block word s = do
	add $ Cmd $ word <> " :"
	mapM_ (add . indent) =<< runM s

-- | Generates shell code to fill a variable with a line read from stdin.
readVar :: Var String -> Script ()
readVar (Var (V { varName = VarName varname })) = add $
	Cmd $ "read " <> getQ (quote varname)

-- | By default, shell scripts continue running past commands that exit
-- nonzero. Use "stopOnFailure True" to make the script stop on the first
-- such command.
stopOnFailure :: Bool -> Script ()
stopOnFailure b = add $ Cmd $ "set " <> (if b then "-" else "+") <> "e"

-- | Makes a nonzero exit status be ignored.
ignoreFailure :: Script () -> Script ()
ignoreFailure s = runM s >>= mapM_ (add . go)
  where
	go c@(Cmd _) = Or c true
	go c@(Comment _) = c
	go (Subshell i l) = Subshell i (map go l)
	-- Assumes pipefail is not set.
	go (Pipe e1 e2) = Pipe e1 (go e2)
	-- Note that in shell, a && b || true will result in true;
	-- there is no need for extra parens.
	go c@(And _ _) = Or c true
	go (Or e1 e2) = Or e1 (go e2)
	go (Redir e r) = Redir (go e) r

	true = Cmd "true"

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

redir :: Script () -> RedirSpec -> Script ()
redir s r = do
	e <- toSingleExp <$> runM s
	add $ Redir e r

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
s |> f = redir s (fileRedir f stdOutput RedirToFile)

-- | Appends to a file. (If file doesn't exist, it will be created.)
(|>>) :: RedirFile f => Script () -> f -> Script ()
s |>> f = redir s (fileRedir f stdOutput RedirToFileAppend)

-- | Redirects standard input from a file.
(|<) :: RedirFile f => Script () -> f -> Script ()
s |< f = redir s (fileRedir f stdInput RedirFromFile)

-- | Redirects a script's output to stderr.
toStderr :: Script () -> Script ()
toStderr s = s &stdOutput>&stdError

-- | Redirects the first file descriptor to output to the second.
--
-- For example, to redirect a command's stderr to stdout:
--
-- > cmd "foo" &stdError>&stdOutput
(>&) :: (Script (), Fd) -> Fd -> Script ()
(s, fd1) >& fd2 = redir s (RedirOutput fd1 fd2)

-- | Redirects the first file descriptor to input from the second.
--
-- For example, to read from Fd 42:
--
-- > cmd "foo" &stdInput<&Fd 42
(<&) :: (Script (), Fd) -> Fd -> Script ()
(s, fd1) <& fd2 = redir s (RedirInput fd1 fd2)

-- | Helper for '>&' and '<&'
(&) :: Script () -> Fd -> (Script (), Fd)
(&) = (,)

-- | Provides the Text as input to the Script, using a here-document.
hereDocument :: Script () -> L.Text -> Script ()
hereDocument s t = redir s (RedirHereDoc t)

-- | This data type represents shell Arithmetic Expressions.
--
-- Note that in shell arithmetic, expressions that would evaluate to a
-- Bool, such as ANot and AEqual instead evaluate to 1 for True and 0 for
-- False.
data Arith
	= ANum Integer
	| AVar (Var Integer)
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
	| ACond Arith Arith Arith -- ^ if the first argument is non-zero, the result is the second, else the result is the third

fmtArith :: Env -> Arith -> L.Text
fmtArith env = go
  where
	go (ANum i) = L.pack (show i)
	-- shell variable must be expanded without quotes
	go (AVar (Var v)) = getQ $ expandVar v env (varName v)
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
	go (ACond c a b) = paren $ go c <> " ? " <> go a <> " : " <> go b

	paren t = "(" <> t <> ")"

	binop a o b = paren $ go a <> " " <> o <> " " <> go b
	unop o v = paren $ o <> " " <> go v
