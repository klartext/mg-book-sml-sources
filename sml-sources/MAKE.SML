(* Dieses Makefile baut das Morphogrammatik Labor, die Implementierung des Buches "Morphogrammatik -- Eine Einf�hrung in die Theorie der Form".

SML aufrufen und  use "make";  eingeben, alles weitere geschieht automatisch. Es wird dann eine ausf�hrbare Datei "MG-LAB" erzeugt, die das vollst�ndige Morphogrammatik Labor enth�lt.*)

use "all";
use "%read.sml";
use "compiler";
use "com41";
use "titel.sml";


(exportML "MG-LAB";titel ());


