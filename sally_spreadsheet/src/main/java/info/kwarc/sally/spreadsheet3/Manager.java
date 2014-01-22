package info.kwarc.sally.spreadsheet3;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.ModelManager;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;
import info.kwarc.sally.spreadsheet3.ontology.SemanticModelManager;


public class Manager {
	
	ConcreteSpreadsheet spreadsheet;
	ModelManager model;
	IOntologyProvider ontology;
	SemanticModelManager semanticModel;

	final Logger logger = LoggerFactory.getLogger(Manager.class);
	
	public Manager(IOntologyProvider ontology) {
		this.spreadsheet = new ConcreteSpreadsheet();
		this.model = new ModelManager();
		this.ontology = ontology;
		this.semanticModel = new SemanticModelManager();
	}

	// ---------- Getters for the different components ----------
	
	public ConcreteSpreadsheet getSpreadsheet() {
		return spreadsheet;
	}

	public ModelManager getModel() {
		return model;
	}

	public IOntologyProvider getOntology() {
		return ontology;
	}

	public SemanticModelManager getSemanticModel() {
		return semanticModel;
	}
	
	// ---------- Methods that need an interaction between different components ----------
	
	public List<Message> addCellToBlock(CellSpaceInformation position, Block block) throws ModelException {
		List<Message> messages = new ArrayList<Message>();

		//Block atomicBlock = model.getOrCreateAtomicBlock(position);
		messages.addAll( model.addCellToBlock(block, position) );
		
		List<Relation> typeRelations = model.getRelationsFor(null, block, Relation.RelationType.TYPERELATION);
		 if (typeRelations.size() != 1)
			 logger.info("No TYPE relation for block. Can not update semantic values.");
		 else {
			 Relation typeRelation = typeRelations.get(0);
			
			 semanticModel.updateSemanticValues(typeRelation, spreadsheet);
			 List<Block> relatedBlocks = semanticModel.getAllBlocksForURI(typeRelation.getUri());
			 messages.addAll( semanticModel.checkBlocksForCompleteness(relatedBlocks, typeRelation.getUri(), spreadsheet));
		 }
		
		return messages;
	}
	
}
