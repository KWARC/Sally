package info.kwarc.sissi.model.document.spreadsheet;

public class IUIQueries {

	/*

// select all functional block instances talking about bolts and linked to a FB talking about total costs

PREFIX rdf:     <http://www.w3.org/1999/02/22-rdf-syntax-ns#> 
PREFIX rdfs:    <http://www.w3.org/2000/01/rdf-schema#>
PREFIX im:      <http://www.kwarc.info/sally/im#>
PREFIX asm:      <http://www.kwarc.info/sally/asm#>
PREFIX csm:      <http://www.kwarc.info/sally/csm#>
PREFIX acm:      <http://www.kwarc.info/sally/acm#>


SELECT ?y ?fbi WHERE {
   ?fbi a asm:FunctionalInstance.
   ?fbi asm:valueOf ?x.
   ?fbi asm:partOfFunctionalBlock ?fb.
   ?fb im:ontologyURI <https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?total>.

   ?x im:ontologyURI ?y.
   ?x rdfs:label ?z.

   ?t im:ontologyURI ?y.
   ?t rdfs:label ?z.

   <http://blah.cad/bolt1> acm:valueOf ?t
}
	 
	 */
	
}
