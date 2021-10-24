(* Dieses Makefile baut das Morphogrammatik Labor, die Implementierung des Buches "Morphogrammatik -- Eine Einföhrung in die Theorie der Form".

SML aufrufen und  use "make";  eingeben, alles weitere geschieht automatisch. Es wird dann eine ausföhrbare Datei "MG-LAB" erzeugt, die das vollstÙndige Morphogrammatik Labor enthÙlt.*)

use "all";
use "%read.sml";
use "compiler";
use "com41";
use "titel.sml";


(exportML "MG-LAB";titel ());


