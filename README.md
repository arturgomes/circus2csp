# Circus to CSPm translator

Our tool translates Circus specifications written in Latex syntax into CSPm code for use in FDR. This is an implementation of the work from Oliveira et. al.*.

The tool is implemented in Haskell, on top of Mark Utting's JAZA (Just Another Z Animator) and extended in order to parse Circus. The tool basically is able to perform both Omega and Upslon transformations as well as to refine Circus using a few selected refinement laws required for the translation purpose.


# How to install

The recommended approach is to use stack
(see [The Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/))
configured as recommended on your platform to ensure that stack-built exectuables
are on your [PATH](https://docs.haskellstack.org/en/stable/install_and_upgrade/#path).

Simply do 'stack install' at the top-level.

It will create and setup an executable called `c2c`.

# Setting **source** and **destination** folders

In Circus2CSP, the user can define a source folder where the Circus files can be found, as well as a destination folder, where the '*.csp' files will be saved. There should be a hidden file called ".c2c" in the folder you want to work with, and then, write the following lines:

```
src:source/directory/of/circus/specs/
dst:destination/directory/to/save/cspm/files

```

# How to run

Go to the directory with the Circus files you want to process, and simply invoke `c2c`.

You will see a command-line interface very similar to that used by Jaza.

Just type ``help`` and you'll see the list of options.

<!-- Translating a Circus .tex file into a CSPm .csp file requires three steps: `load`, `omega` and `tocsp`. -->

<!-- Other commands are mainly for debugging purposes and are generally not very helpful. -->

### Loading a file
In order to load a file, enter the following code, with **filename** being the name of your file
without the extension .tex
```
load filename
```
The filename path, if relative, is relative to the directory from which `c2c` was launched.

### From Circus to State-free CSP

To transalate loaded Circus to state-free CSP, along with a memory model,
 use  `omega`.

### From State-free CSP to CSPm

To translate state-free CSP plus memory model to CSPm, use `tocsp`.

The result of the translation will produce a file *.csp with the new spec ready to run on FDR. You'll have to bundle copies of the files **function_aux.csp** and **sequence_aux.csp** along with the generated code, in order to use FDR. Both files contains auxiliary definitions regarding sets and sequences. These are very important and useful.


# Ones we made up earlier

Example Circus files can be found in various subdirectories of the top-level `exs` directory.
Within that the `cases` sub-directory contains the main case-studies driving the development of `c2c`.

# References

* Oliveira M.V.M., Sampaio A.C.A., Conserva Filho M.S. (2014) Model-Checking Circus State-Rich Specifications. In: Albert E., Sekerinski E. (eds) Integrated Formal Methods. IFM 2014. Lecture Notes in Computer Science, vol 8739. Springer, Cham

# CHANGELOG

## 0.8.1.0 - July 2018

Now we have the .c2c file where the user can direct the source folder (where the Circus specs are) and the destination (where the CSPm files should be created).


## 0.8.0.0 - April 2018

Lots of reworking and tidying up, as well as many enhancements to the memory model. Also verifications and proof of the correctness of the memory revisions.

## 0.7b - September 2017

I've removed all the unused files from JAZA and also fixed the migration to GHC 7.10. Now we don't get those weird messages of "No instance for (Applicative ...)".

## 0.6b - September 2017

Now every variable in the AST has a third field, its type. The translator
will be in charge of filling all those fields with the respective type
of the variable.
Moreover, now we have a correct implementation of the multiple bindings
since the Circus specification. What it was doing before was to
translate into CSP with the definitions being made directly into the CSP text.
Now it comes from the AST and the mapping functions.

## 0.5
Now that we can load the files without the extension .tex, we produce
two other files : .hc and .csp on the same folder of the .tex file:
    .hc is the file containing the haskell AST representation of the spec
    .csp is the translated specification in CSP
Now we also load multiple processes within the same file without name
clashing.
We also are able to have tailored Memory and Memorise actions within
a CSP process with respect only to the types used within the scope
of that process.
