# Circus to CSPm translator

Our tool translates Circus specifications written in Latex syntax into CSPm code for use in FDR. This is an implementation of the work from Oliveira et. al.*.

The tool is implemented in Haskell, on top of Mark Utting's JAZA (Just Another Z Animator) and extended in order to parse Circus. The tool basically is able to perform both Omega and Upslon transformations as well as to refine Circus using a few selected refinement laws required for the translation purpose.

In our testings we use GHC version 7.8.4


# How to install

Once you have cloned/downloaded this project, you should then write:

```
make circus
```

It will build the translator tool with a binary file "circus".

# How to run

If you're familiar with JAZA, you'll see a very similar prompt. Just type ``help`` and you'll see the list of options.

## Loading a file
In order to load a file, enter the following code, with **filename** being the name of your file 
without the extension .tex
```
load filename
```

## Printing a file
If you want to display the current loaded specification, write ``show`` on the prompt, and it will print the entire specification. It will also generate a file **spec.txt** so you can open it in your text editor.

## Applying Omega functions

Then you'll be able to apply the omega transformation, just typing ``omega``. The operation is done if no warnings is shown. Hit ``show`` again and see the result from the operation. A *.hc file is produced with the Haskell representation of the specification. This can later on be translated back to latex.

## From Circus to CSP

After executing the ``omega`` operation, the final operation is the ``tocsp`` so you can use it in FDR.

The result of the translation will produce a file *.csp with the new spec ready to run on FDR. You'll have to copy the files **function_aux.csp** and **sequence_aux.csp** along with the generated code, in order to use FDR. Both files contains auxiliary definitions regarding sets and sequences. These are very important and useful. 


# References

* Oliveira M.V.M., Sampaio A.C.A., Conserva Filho M.S. (2014) Model-Checking Circus State-Rich Specifications. In: Albert E., Sekerinski E. (eds) Integrated Formal Methods. IFM 2014. Lecture Notes in Computer Science, vol 8739. Springer, Cham

# CHANGELOG

## 
New version 0.5
Now that we can load the files without the extension .tex, we produce
two other files : .hc and .csp on the same folder of the .tex file:
    .hc is the file containing the haskell AST representation of the spec
    .csp is the translated specification in CSP
Now we also load multiple processes within the same file without name
clashing.
We also are able to have tailored Memory and Memorise actions within
a CSP process with respect only to the types used within the scope
of that process.
