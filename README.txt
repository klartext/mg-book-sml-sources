This repository contains the sourcecode of the following book:
==============================================================

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


--------------------------------------------------------------------------------
One file for is missing here, and it is a file from the book
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
Compilation of the sources will not work with current SML compilers.
The reason is that in 1997 'value restriction' was added to SML.
It's intended to change the code here, so that it can be compiled with current
SML compilers.

It's also intended here to use this old code as a reference implementation,
providing test cases for a newer implementation using OCaml.
--------------------------------------------------------------------------------
Explanation of the value restriction:
  http://mlton.org/ValueRestriction
--------------------------------------------------------------------------------
