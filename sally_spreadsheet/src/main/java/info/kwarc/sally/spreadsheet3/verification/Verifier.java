package info.kwarc.sally.spreadsheet3.verification;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import info.kwarc.sally.spreadsheet3.Manager;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;
import info.kwarc.sally.spreadsheet3.ontology.OntologyException;

public class Verifier {
	
	
	Z3Interface z3;
	
	Manager manager;
	
	List<DataSymbolInformation> dataSymbols;
	Map<CellSpaceInformation, String> semanticMapping;
	boolean ready = false;
	
	final Logger logger = LoggerFactory.getLogger(Verifier.class);
	
	public Verifier(Manager manager) throws ModelException, OntologyException {
		this.manager = manager;
		reinit();
	}
	
	public void reinit() throws ModelException, OntologyException {
		semanticMapping = manager.getModel().getCompleteSemanticMapping(manager.getSpreadsheet(), manager.getOntology());
		
		dataSymbols = VerificationDataExtractor.extractDataTypes(manager.getModel().getBlockTypes(manager.getModel().getAllTopLevelBlocks()), manager.getSpreadsheet());
		
		z3 = new Z3Interface();
		// Specification of symbols, axioms and functions
		List<String> specification = new ArrayList<String>();
		specification.add( VerificationSpecificationGenerator.getObjectSymbolSpecification(dataSymbols));		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntology().getAllBasicFunctionObjects(), manager));
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntology().getAllBasicFunctionObjects(), manager, dataSymbols));
		specification.addAll( VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSymbols) );
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntology().getAllDomainFunctionObjects(), manager));
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntology().getAllDomainFunctionObjects(), manager, dataSymbols));
		specification.addAll( VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataSymbols));
		
		for (AxiomObject axiom : manager.getOntology().getAxioms())
			specification.add(VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSymbols));
		
		if (!z3.verify(specification, false).equals(VerificationStatusIntern.SAT)) {
			logger.error("Background knowledge is not consistent. Verification is not possible.");
			ready = false;
		} else
			ready = true;
	}
	
	public VerificationStatus checkValue(CellSpaceInformation position) {
		VerificationStatus status = VerificationStatus.ERROR;
		
		if (ready) {
			boolean symbolFound = false;
			for (int i = 0; (i < dataSymbols.size()) && !symbolFound; i++) {
				DataSymbolInformation symbol = dataSymbols.get(i);
				if (symbol.getPostition().equals(position)) {
					symbolFound = true;
					switch (z3.verify(VerificationSpecificationGenerator.createSymbolValueAssertion(manager, symbol), true)) {
					case SAT:
						status = VerificationStatus.VERIFIED;
						break;
					case UNSAT:
						status = VerificationStatus.FAILED;
						break;
					case ERROR:
						logger.error("Error in value verification.");
						break;
					}
				}
			}
		}
		return status;
	}
	
	public VerificationStatus checkAllValues() {
		VerificationStatus status = VerificationStatus.ERROR;
		
		if	(ready) {
			List<String> specification = new ArrayList<String>();
			
			for (DataSymbolInformation symbol : dataSymbols)
				specification.add(VerificationSpecificationGenerator.createSymbolValueAssertion(manager, symbol));
				
			switch (z3.verify(specification, true)) {
			case SAT:
				status = VerificationStatus.VERIFIED;
				break;
			case UNSAT:
				status = VerificationStatus.FAILED;
				break;
			case ERROR:
				logger.error("Error in value verification.");
				break;
			}
		}
		
		return status;
	}
	
	public VerificationStatus checkCPSimilarBlock(CPSimilarBlockData block) {
		VerificationStatus status = VerificationStatus.ERROR;
		
		if	(ready) {	
			switch (z3.verify(VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, block, dataSymbols), true)) {
			case SAT:
				status = VerificationStatus.FAILED;		// SAT = It is possible that the formula is not equal to the ontolgoy function
				break;
			case UNSAT:
				status = VerificationStatus.VERIFIED;	// UNSAT = It is impossible that the formula is not equal to the ontolgoy function
				break;
			case ERROR:
				logger.error("Error in value verification.");
				break;
			}
		}
		
		return status;
	}
	
	public VerificationStatus checkFunction(CellSpaceInformation position, Relation relation) throws ModelException {
		VerificationStatus status;
		String formula = manager.getSpreadsheet().get(position).getFormula();
		if (formula.isEmpty() || !relation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION) )
			status = VerificationStatus.VERIFIED;
		else if (!ready)
			status = VerificationStatus.ERROR;
		else {	
			String specification = VerificationSpecificationGenerator.getFormulaSpec(manager, relation, formula, position, semanticMapping, dataSymbols) ;
			switch ( z3.verify(specification, true) ) {
			case SAT:
				status = VerificationStatus.FAILED;		// SAT = It is possible that the formula is not equal to the ontology function
				logger.info("Function-Verification faild. Position: " + position.toString() + " Formula: " + formula);
				break;
			case UNSAT:
				status = VerificationStatus.VERIFIED;	// UNSAT = It is impossible that the formula is not equal to the ontology function
				break;
			default:
				status = VerificationStatus.ERROR;
				logger.error("Error in value verification.");
				break;
			}	
		}
		
		return status;
	}

	public VerificationStatus checkRelation(Relation relation) throws ModelException {
		VerificationStatus status;
		
		if	(!relation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION))
			status = VerificationStatus.VERIFIED;
		else if (!ready)
			status = VerificationStatus.ERROR;
		else {
			status = VerificationStatus.VERIFIED;	// Before you leave the bed everything is OK :-).
			for (CellTuple cellRelation : relation.getCellRelations()) {
				if (status == VerificationStatus.VERIFIED)
					status = checkFunction(cellRelation.getTuple().get(cellRelation.getTuple().size()-1), relation);	
			}
		}
		
		return status;
	}
	
	public VerificationStatus checkAllFunctions() throws ModelException {
		VerificationStatus status = VerificationStatus.VERIFIED;
		
		for (Relation relation : manager.getModel().getRelationsFor(null, null, Relation.RelationType.FUNCTIONALRELATION)) 
			if (status == VerificationStatus.VERIFIED)
				status = checkRelation(relation);
	
		/*if (!ready)
			status = VerificationStatus.ERROR;
		else {
			status = VerificationStatus.VERIFIED;		// Before you leave the bed everything is OK :-).
			for (Relation relation : manager.getRelationsFor(null, null, Relation.RelationType.FUNCTIONALRELATION)) {
				for (CellTuple cellRelation : relation.getCellRelations()) {
					if (status == VerificationStatus.VERIFIED)
						status = checkFunction(cellRelation.getTuple().get(cellRelation.getTuple().size()-1), relation);
				}
			}
		}*/
		
		return status;
	}
	
	public void printDebugOutput() {
		z3.printCompleteSpecification();
	}

}
