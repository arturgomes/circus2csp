{-# LANGUAGE CPP #-}
module Test where

#if (__GLASGOW_HASKELL__ >= 710)
hversion = "I am late"
#endif

#if (__GLASGOW_HASKELL__ < 710)
hversion = "I am early"
#endif