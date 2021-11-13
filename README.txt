This repository contains sourcecode of the following book:
==========================================================

--------------------------------------------------------------------------------
Thomas Mahler & Rudolf Kaehr
Morphogrammatik: Eine Einführung in die Theorie der logischen Form

Thomas Mahler & Rudolf Kaehr: „Morphogrammatik: Eine Einführung in die Theorie
der logischen Form“ in: www.vordenker.de (Sommer Edition 2017) J. Paul (Ed.)
URL: http://www.vordenker.de/rk/tm-rk_Morphogrammatik_Buch_1993.pdf —
originally published in: Klagenfurter Beiträge zur Technikdiskussion, (A.
Bammé, P. Baumgartner, W. Berger, E. Kotzmann, Eds.), Heft 65, Klagenfurt 1993
[ https://ubdocs.uni-klu.ac.at/open/voll/tewi/AC00847057.pdf]
--------------------------------------------------------------------------------
This description has been found here:
  https://www.vordenker.de/rk/rk_bibliographie.htm
--------------------------------------------------------------------------------

The License is Apache2 License, as stated by Thomas Mahler.
See file LICENSE-2.0.txt for details.


The code can be found in the directory "sml-sources".

--------------------------------------------------------------------------------
One file that was included in the book is missing here; it is a file from the book
"ML for the Working Programmer".
For license issues see here: https://www.cl.cam.ac.uk/~lp15/MLbook/

The version used in the MG-book is that from 1991.
It looks like it is not available anymore.

There is that file from the 2nd edition, which you can get it here:
  https://www.cl.cam.ac.uk/~lp15/MLbook/programs/sample9.sml

But it looks like the version from the first edition must be scraped from the
morphogrammatics book (see link above), page 251 (pdf-page 262).

For changes of the sources (and the SML copilers),
please see here:
  https://www.cl.cam.ac.uk/~lp15/MLbook/
--------------------------------------------------------------------------------

The original SML sources from the MG-Book failed to compile.
The reason is that in 1997 'value restriction' was added to SML.
( For explanation of the value restriction, see here for example: http://mlton.org/ValueRestriction )

In the meantime the code has been changed, so that it now compiles.
You can use it interactively with SMLNJ:

Try it with
  $ smlnj all.sml
and have fun.
--------------------------------------------------------------------------------

Implementation of parts of the code are now also available in Haskell and OCaml.

--------------------------------------------------------------------------------
