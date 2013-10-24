package info.kwarc.sally.spreadsheet3.export;

import info.kwarc.sally.model.ontology2.ASM;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;

import java.util.HashMap;
import java.util.Map;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;

public class ModelRDFExport {

	public static Model getRDF(Manager manager, String fileName) {
		Model model = ModelFactory.createDefaultModel();
		model.setNsPrefix("asm", ASM.getURI());
		model.setNsPrefix("rdf", RDF.getURI());
		
		Resource root = model.createResource();
		model.add(root, ASM.partOfFile, model.createLiteral(fileName));
		model.add(root, RDF.type, ASM.AbstractSpreadsheetModelType);
		Map<Block, Resource> blockResources =new HashMap<Block, Resource>();
		
		for (Block block : manager.getAllBlocks()) {
			Resource blkResource = model.createResource();
			blockResources.put(block, blkResource);
			model.add(blkResource, ASM.blockID, model.createLiteral(Integer.toString(block.getId())));
			model.add(blkResource, ASM.partOfASM, root);
			model.add(blkResource, RDF.type, ASM.Block);
			model.add(blkResource, ASM.hasSheet, block.getWorksheet());
			model.add(blkResource, ASM.hasStartRow, Integer.toString(block.getMinRow()));
			model.add(blkResource, ASM.hasEndRow, Integer.toString(block.getMaxRow()));
			model.add(blkResource, ASM.hasStartCol, Integer.toString(block.getMinColumn()));
			model.add(blkResource, ASM.hasEndCol, Integer.toString(block.getMaxColumn()));
		}
		
		for (Relation rel : manager.getAllRelations()) {
			Resource relResource = model.createResource();
			model.add(relResource, ASM.relType, rel.getRelationType().name());
			model.add(relResource, ASM.partOfASM, root);
			model.add(relResource, ASM.hasURL, rel.getUri());
			model.add(relResource, RDF.type, ASM.Relation);

			RDFNode [] nodes = new RDFNode[rel.getBlocks().size()];
			int index = 0;
			for (Block blk : rel.getBlocks()) {
				nodes[index++] = blockResources.get(blk);
			}

			model.add(relResource, ASM.hasArgs, model.createList(nodes));
		}
		return model;
	}
	
}
