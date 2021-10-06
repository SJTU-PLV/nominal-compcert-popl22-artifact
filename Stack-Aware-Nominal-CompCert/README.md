# Nominal CompCert

## Overview
We replaced the "nextblock" design in CompCert by "support and freshness" which comes from Nominal Technique.

This version uses Module Type to describe the necessary properties (definitions and theorems) of "block" and "sup" Type for the original compilation pass. 

We have repaired the whole proof using "Declare Module sup:SUP (block:BLOCK)". We have also made the compiler available using "positive" and "positive list" to realize "block" and "sup". While the code is the same except the definition of these two Modules. 

We optimistically believe that we can design different "block" and "sup" types which satisfy our signature to carry more information and improve/extend the original CompCert without breaking the proves we do not concern.
