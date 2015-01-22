-- -*- idris-packages: ("effects") -*-
-- Remember to ask Idris to load the effects package with this file!
-- That's "-p effects" on the command line, or set the `idris-packages'
-- variable in Emacs.

module Exercises3

import Effects
import Effect.File

%default total

-- * Prove associativity of Nat addition using pattern-matching and
-- using tactics.

-- * Implement an effect and handlers that writes the text "BEEP" to
-- the console.

-- ** Implement an effect called SLEEP with an operation called sleep
-- that causes execution to pause. You may need to read about the C
-- FFI in the tutorial.

-- *** Write an effect that allows you to write the text "BEEPIER" to
-- the console up to 3 times, but no more. Hint: parametrize the state
-- with the following:

data BeepierState : Maybe Nat -> Type where
  NoBeeps : BeepierState Nothing
  BeepsPossible : (n : Nat) -> BeepierState (Just n)


-- *** Use the SDL bindings at https://github.com/edwinb/SDL-idris to
-- animate a bouncing ball in a window.

-- *** Extend the SDL bindings with a missing primitive from the SDL
-- library, and send a pull request upstream.
