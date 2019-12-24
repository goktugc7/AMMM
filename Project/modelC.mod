/*********************************************
 * OPL 12.8.0.0 Model
 * Author: Goktug
 * Creation Date: Dec 23, 2019 at 5:34:33 PM
 *********************************************/

 int nClasses = ...;
 int nOptions = ...;
 range O = 1..nOptions;
 range C = 1..nClasses;
 
 int carsOfClass[c in C] = ...;
 int classOption[c in C][o in O] = ...;              
 int m[o in O] = ...;
 int k[o in O] = ...;

 int nPositions; 
 execute {
 	nPositions = 0;
 	for (var c = 1; c <= nClasses; ++c)
 		nPositions += carsOfClass[c];
 }
 
 range P = 1..nPositions; 
 // IMPORTANT HINT!!!!!!
 // A position p in P is a possible starting point of a window for option o iff p + k[o] - 1 <= nPositions.
 // The window itself is [ p...(p+k[o]-1) ]
 
 dvar boolean pc[p in P][c in C];
 dvar boolean po[p in P][o in O];
 
 
 maximize sum(o in O)
 			sum(p in 1..(nPositions-k[o]+1))
 	    		((sum(i in p..(p+k[o]-1))
 	      			po[i][o]) <= m[o]);
  
 subject to {
 	forall (p in P)
 	  sum(c in C)(pc[p][c]) == 1;
 	
 	forall(p in P, c in C, o in O)
 	  (pc[p][c] == 1) => po[p][o] == classOption[c][o];
 	
 	forall(c in C)
 	  sum(p in P)
 	    pc[p][c] == carsOfClass[c];
 }
 
 execute {
  	var solution = new Array(1+nPositions);
 	write("SEQUENCE OF CLASSES: ");
 	for (var p = 1; p <= nPositions; ++p) {
 		var placed = 0; 
 		var cl;
 		for (var c = 1; c <= nClasses; ++c) if (pc[p][c] == 1) {++placed; cl = c;}
 		if (placed == 0) {writeln("ERROR: In position " + p + " there is no car"); stop();}
 		else if (placed > 1) {writeln("ERROR: In position " + p + " there is more than one car");stop();}
 		else {solution[p] = cl; write(cl + " ");} 		 
 	}
 	writeln();writeln();
 	for (var o = 1; o <= nOptions; ++o) {
 	 	
 		var violations = 0;
 	 	var solOpt = new Array(1+nPositions);
 		write("OPTION " + o + ":            ");
 		for (var p = 1; p <= nPositions; ++p) { 		 	 	
 			if (classOption[solution[p]][o] == 1) {write("X "); solOpt[p] = 1;}
 			else {write(". "); solOpt[p] = 0;}
        }    		
 		
 		for (p = 1; p + k[o] - 1 <= nPositions; ++p) {
 			placed = 0;
 			for (var pp = p; pp <= p + k[o] - 1; ++pp) {
 				if (solOpt[pp] == 1) ++placed;
  			} 			 			
 			if (placed > m[o]) { 			 			
 				if (violations == 0) write("\tViolations in windows: ");
 				++violations;
 				write("[" + p  + "..." + (p + k[o] - 1) + "] ");
   			} 				 			 		 		
 		}
 		
 		writeln();
 	} 		 		 	
 	
 }  
 
 