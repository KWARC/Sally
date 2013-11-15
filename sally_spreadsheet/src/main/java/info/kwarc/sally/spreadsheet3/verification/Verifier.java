package info.kwarc.sally.spreadsheet3.verification;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;

public class Verifier {
	
	Z3Interface z3;
	Manager manager;
	FormalSpreadsheet spreadsheet;
	List<DataSymbolInformation> dataSymbols;
	Map<CellSpaceInformation, String> semanticMapping;
	boolean ready = false;
	
	final Logger logger = LoggerFactory.getLogger(Verifier.class);
	
	public Verifier(Manager manager, FormalSpreadsheet spreadsheet) {
		this.manager = manager;
		this.spreadsheet = spreadsheet;
		reinit();
	}
	
	public void reinit() {
		semanticMapping = manager.getCompleteSemanticMapping(spreadsheet);
		
		dataSymbols = VerificationDataExtractor.extractDataTypes(manager.getBlockTypes(manager.getAllTopLevelBlocks()), spreadsheet);
		
		z3 = new Z3Interface();
		// Specification of symbols, axioms and functions
		List<String> specification = new ArrayList<String>();
		specification.add( VerificationSpecificationGenerator.getObjectSymbolSpecification(dataSymbols));		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllBasicFunctionObjects(), manager));
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllBasicFunctionObjects(), manager, dataSymbols));
		specification.addAll( VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSymbols) );
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllDomainFunctionObjects(), manager));
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllDomainFunctionObjects(), manager, dataSymbols));
		specification.addAll( VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataSymbols));
		
		for (AxiomObject axiom : manager.getOntologyInterface().getAxioms())
			specification.add(VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSymbols));
		
		if (!z3.verify(specification, false).equals(VerificationStatus.SAT)) {
			logger.error("Background knowledge is not consistent. Verification is not possible.");
			ready = false;
		} else
			ready = true;
	}
	
	public VerificationStatus checkValue(CellSpaceInformation position) {
		VerificationStatus status = VerificationStatus.FAILED;
		
		if (ready) {
			boolean symbolFound = false;
			for (int i = 0; (i < dataSymbols.size()) && !symbolFound; i++) {
				DataSymbolInformation symbol = dataSymbols.get(i);
				if (symbol.getPostition().equals(position)) {
					symbolFound = true;
					status = z3.verify(VerificationSpecificationGenerator.createSymbolValueAssertion(manager, symbol), true);
				}
			}
		}
		return status;
	}
	
	public VerificationStatus checkAllValues() {
		VerificationStatus status = VerificationStatus.FAILED;
		
		if	(ready) {
			List<String> specification = new ArrayList<String>();
			
			for (DataSymbolInformation symbol : dataSymbols)
				specification.add(VerificationSpecificationGenerator.createSymbolValueAssertion(manager, symbol));
				
			status = z3.verify(specification, true);
		}
		
		return status;
	}
	
	public VerificationStatus checkCPSimilarBlock(CPSimilarBlockData block) {
		VerificationStatus status = VerificationStatus.FAILED;
		
		if	(ready) {	
			status = z3.verify(VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, block, dataSymbols), true);
		}
		
		return status;
	}
	
	public VerificationStatus checkFunction(CellSpaceInformation position, Relation relation) {
		VerificationStatus status = VerificationStatus.FAILED;
		
		if	(ready) {	
			String formula = spreadsheet.get(position).getFormula();
			if (!formula.isEmpty() && relation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION) ) {
				String specification = VerificationSpecificationGenerator.getFormulaSpec(manager, relation, formula, position, semanticMapping, dataSymbols) ;
				status = z3.verify(specification, true);
			}
				
		}
		
		return status;
	}
	
	public VerificationStatus checkAllFunctions() {
		VerificationStatus status = VerificationStatus.FAILED;
		
		if	(ready) {
			List<String> specification = new ArrayList<String>();
			for (Relation relation : manager.getRelationsFor(null, null, Relation.RelationType.FUNCTIONALRELATION)) {
				for (CellTuple cellRelation : relation.getCellRelations()) {
					CellSpaceInformation position = cellRelation.getTuple().get(cellRelation.getTuple().size()-1);
					String formula = spreadsheet.get(position).getFormula();
					if (!formula.isEmpty() ) 
						specification.add(VerificationSpecificationGenerator.getFormulaSpec(manager, relation, formula, position, semanticMapping, dataSymbols) );
						
				}
			}
			status = z3.verify(specification, true);
		}
		
		return status;
	}
	
	public VerificationStatus checkRelation(Relation relation) {
		VerificationStatus status = VerificationStatus.FAILED;
		
		if	(ready && relation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION)) {
			List<String> specification = new ArrayList<String>();
			
			for (CellTuple cellRelation : relation.getCellRelations()) {
				CellSpaceInformation position = cellRelation.getTuple().get(cellRelation.getTuple().size()-1);
				String formula = spreadsheet.get(position).getFormula();
				if (!formula.isEmpty() ) 
					specification.add(VerificationSpecificationGenerator.getFormulaSpec(manager, relation, formula, position, semanticMapping, dataSymbols) );
					
			}
			
			if (!specification.isEmpty())
				status = z3.verify(specification, true);
		}
		
		return status;
	}
	
	public void printDebugOutput() {
		z3.printCompleteSpecification();
	}

}
