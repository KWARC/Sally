package info.kwarc.sally.spreadsheet3.extraction;

import info.kwarc.sally.spreadsheet3.ContentValueType;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.rapidminer.Process;
import com.rapidminer.RapidMiner;
import com.rapidminer.example.ExampleSet;
import com.rapidminer.operator.IOContainer;
import com.rapidminer.operator.Operator;
import com.rapidminer.operator.OperatorException;
import com.rapidminer.operator.ProcessRootOperator;
import com.rapidminer.tools.LogService;

/**
 * A class to classify cells of a worksheet as legend of functional block cells based on heuristics or a decision tree. 
 * @author cliguda
 *
 */
public class CellClassifier {

	
	Process classifier = null;
	String[] attributeNames;
	
	final Logger logger = LoggerFactory.getLogger(CellClassifier.class);
	
	public CellClassifier(String process, String model, String[] attributes) {
		this.attributeNames = attributes;
		
		try {
			System.setProperty("rapidminer.home", System.getProperty("user.dir") + "\\lib\\Rapidminer-5.2");
		
			RapidMiner.init();
			classifier = new Process(new File(process));
			classifier.getOperator("Read Model").setParameter("model_file", model);
			classifier.getRootOperator().setParameter(ProcessRootOperator.PARAMETER_LOGVERBOSITY, new Integer(com.rapidminer.tools.LogService.OFF).toString());
			LogService.getGlobal().setVerbosityLevel(com.rapidminer.tools.LogService.OFF);
		} catch (Exception e) {
			logger.info("Exception Message: " + e.getMessage());
		} 
	}
	
	/*
	public CellAttributeInformation[][] classify(Sheet sheet, ExtractionParameter parameter) {
		logger.debug("Start classifying...");
		CellAttributeInformation[][] cellInformation = new CellAttributeInformation[sheet.getMaxRow()][];
		Boolean[][] missingLegend = new Boolean[sheet.getMaxRow()][];
		
		// Preprocessing - setting hidden and empty cells
		for (int row = 0; row < sheet.getMaxRow(); row++) {
			cellInformation[row] = new CellAttributeInformation[sheet.getMaxColumn()];
			missingLegend[row] = new Boolean[sheet.getMaxColumn()];
			for (int column = 0; column < sheet.getMaxColumn(); column++) {
				missingLegend[row][column] = false;
				Cell cell = sheet.getCellForPosition(row, column);
				if (cellInformation[row][column] == null) {
					if (cell.getContent().isEmpty())
						cellInformation[row][column] = createLocalAttributes(sheet, row, column, StructureType.EMPTY);
					else if (parameter.textAsLegend && cell.getFormula().isEmpty() && (Util.isString(cell.getContent()))) {
						cellInformation[row][column] = createLocalAttributes(sheet, row, column, StructureType.LEGEND);
					} else 
						cellInformation[row][column] = createLocalAttributes(sheet, row, column, StructureType.UNKNOWN);
					CellSpaceInformation pos = cell.getPosition();
					for(int i = pos.getRow(); i < pos.getRow() + pos.getHeight(); i++) {
						for (int j = pos.getColumn(); j < pos.getColumn() + pos.getWidth(); j++)
							if ((i > pos.getRow()) || (j > pos.getColumn()) )
									cellInformation[i][j] = createLocalAttributes(sheet, row, column, StructureType.HIDDEN);;
					}
				}
			}
		}
		
		// Now we start to classify
		if (classifier != null) {	
			int diagonalBorder = java.lang.Math.min(sheet.getMaxRow(), sheet.getMaxColumn());
			// First we classify in diagonal direction.
			for (int index = 0; index < diagonalBorder; index++) {
				// Classify one row
				for (int column = index; column < sheet.getMaxColumn(); column++) 
					classifyCell(cellInformation, index, column, sheet);
				
				// Classify one column
				for (int row = index+1; row < sheet.getMaxRow(); row++)
					classifyCell(cellInformation, row, index, sheet);

			}
		}
		
		// Postprocessing
		CellClassificationPostProcessor.processSheet(cellInformation, sheet);
		
		logger.debug("Classifying finished.");
		return cellInformation;
	}*/
	
	/**
	 * Classifies a complete worksheet.
	 * The used heuristics can be specified by the extraction parameter.
	 */
	public CellAttributeInformation[][] classify(Sheet sheet, ExtractionParameter parameter, Map<CellSpaceInformation, psf.ParserResult> cellFormulae) {
		
		CellAttributeInformation[][] cellInformation = prepocessing(sheet, parameter, cellFormulae);
		Map<CellAttributeInformation, Integer> classificationCache = new HashMap<CellAttributeInformation, Integer>();
		
		logger.debug("Preprocessing:");
		for (int row = 0; row < sheet.getMaxRow(); row++) {
			String classification = "";
			for (int column = 0; column < sheet.getMaxColumn(); column++) {
				classification += "(" + row + "/" + column + ") " + " [";
				if (cellInformation[row][column].getCellType() == StructureType.FB)
					classification += "FB";
				else if (cellInformation[row][column].getCellType() == StructureType.LEGEND)
					classification += "LE";
				else if (cellInformation[row][column].getCellType() == StructureType.LEGENDHEADER)
					classification += "LH";
				else if (cellInformation[row][column].getCellType() == StructureType.EMPTY)
					classification += "E";
				else if (cellInformation[row][column].getCellType() == StructureType.HIDDEN)
					classification += "H";
				else 
					classification += "U";
				classification += "] | ";
			} 
			logger.debug(classification);
		}
		
		// Now we start to classify
		if (classifier != null) {	
			for (int row = 0; row < sheet.getMaxRow(); row++) {
				for (int column = 0; column < sheet.getMaxColumn(); column++) {
					CellAttributeInformation ci = cellInformation[row][column];
					ci.setSurroundingLegends(CellAttributeInformationUtil.hasAssocLegends(cellInformation, row, column));
					if (row > 0)
						ci.setTypeTop(cellInformation[row-1][column].getCellType());
					else
						ci.setTypeTop(StructureType.EMPTY);
					
					if (column > 0)
						ci.setTypeLeft(cellInformation[row][column-1].getCellType());
					else
						ci.setTypeLeft(StructureType.EMPTY);
					
					classifyCell(cellInformation, row, column, sheet, classificationCache);
				}
			}
		}
		// Postprocessing
		CellClassificationPostProcessor.processSheet(cellInformation, sheet);
		
		return cellInformation;
	}
	
	private CellAttributeInformation[][] prepocessing(Sheet sheet, ExtractionParameter parameter, Map<CellSpaceInformation, psf.ParserResult> cellFormulae) {
		
		CellAttributeInformation[][] cellInformation = new CellAttributeInformation[sheet.getMaxRow()][];
		// Initialize
		for (int row = 0; row < sheet.getMaxRow(); row++) {
			cellInformation[row] = new CellAttributeInformation[sheet.getMaxColumn()];
			for (int column = 0; column < sheet.getMaxColumn(); column++) {
				cellInformation[row][column] = CellAttributeInformationUtil.createLocalAttributes(sheet, row, column, StructureType.UNKNOWN);
			}
		}
		
		// Preprocessing - using heuristics
		for (int row = 0; row < sheet.getMaxRow(); row++) {
			//cellInformation[row] = new CellAttributeInformation[sheet.getMaxColumn()];
			for (int column = 0; column < sheet.getMaxColumn(); column++) {
				Cell cell = sheet.getCellForPosition(row, column);
				if (cellInformation[row][column].getCellType() == StructureType.UNKNOWN) {
					if ( cell == null || cell.getContent().isEmpty() ) {
						cellInformation[row][column].setCellType(StructureType.EMPTY);
					} else if (cell.getFormula().isEmpty() && (Util.isString(cell.getContent())) && parameter.isTextAsLegend() ) {
						cellInformation[row][column].setCellType(StructureType.LEGEND);
					} else if (!cell.getFormula().isEmpty() && parameter.isFormulaAsFB()) {
						cellInformation[row][column].setCellType(StructureType.FB);
						psf.ParserResult cellFormula = cellFormulae.get(new CellSpaceInformation(sheet.getId(), row, column));
					
						for (psf.CellPosition refCell : cellFormula.getReferencedPositions()) {
							
							if (refCell.getWorksheet().isEmpty() && (refCell.getRow() < sheet.getMaxRow()) && (refCell.getColumn() < sheet.getMaxColumn()))
								cellInformation[refCell.getRow()][refCell.getColumn()].setCellType(StructureType.FB);
						}
					} else if (!cell.getContent().isEmpty() && Util.identifyValueType(cell.getContent()).equals(ContentValueType.FLOAT) && parameter.isDoubleAsFB())
						cellInformation[row][column].setCellType(StructureType.FB);
					if (cell != null)
						CellClassificationPostProcessor.processCell(sheet, cell, cellInformation);
				}
			}
		}

		return cellInformation;
	}
	
	/*private void classifyCell(CellAttributeInformation[][] cellInformation, int row, int column, Sheet sheet) {
		if (cellInformation[row][column].getCellType().equals(StructureType.UNKNOWN)) {
			cellInformation[row][column] = createAttributes(sheet, row, column, cellInformation);
			int predictionClass = classifyAttributes(cellInformation[row][column].getRapidRepresentation());
			if (predictionClass != -1) {
				cellInformation[row][column].setCellType(StructureType.cellTypeValues[predictionClass]);
			}
		}
		CellClassificationPostProcessor.processCell(sheet.getCellForPosition(row, column), cellInformation);
	}*/
	
	private void classifyCell(CellAttributeInformation[][] cellInformation, int row, int column, Sheet sheet, Map<CellAttributeInformation, Integer> classificationCache) {
		if (cellInformation[row][column].getCellType().equals(StructureType.UNKNOWN)) {
			cellInformation[row][column] = CellAttributeInformationUtil.createAttributes(sheet, row, column, cellInformation);
			if (classificationCache.containsKey(cellInformation[row][column])) {
				cellInformation[row][column].setCellType(StructureType.cellTypeValues[classificationCache.get(cellInformation[row][column])]);
			} else {
				int predictionClass = classifyAttributes(cellInformation[row][column].getNumberRepresentation());
				classificationCache.put(cellInformation[row][column], predictionClass);
				if (predictionClass != -1) {
					cellInformation[row][column].setCellType(StructureType.cellTypeValues[predictionClass]);
				}
			}
		}
		if (sheet.getCellForPosition(row, column) != null)
			CellClassificationPostProcessor.processCell(sheet, sheet.getCellForPosition(row, column), cellInformation);
	}
	
	public int classifyAttributes(Float[] attributes) {
		int predictionClass = -1;
		if (classifier != null) {
			Operator opData = classifier.getOperator("Generate Data by User Specification");
			opData.setListParameter("attribute_values",  createAttribute(attributes));
			try {
				IOContainer resultContainer = classifier.run();
				ExampleSet resultsSet = (ExampleSet) resultContainer.getElementAt(0);
				predictionClass = new Double(resultsSet.getExample(0).getPredictedLabel()).intValue();

				if (predictionClass == 0)   // Rapidminer return 0 of 2.
					predictionClass = 2;
			} catch (OperatorException e) {
				logger.info("Exception Message: " + e.getMessage());
			}
		}
		return predictionClass;
	}
	
	
	private List<String[]> createAttribute(Float[] values) {
		List<String[]> attributes = new ArrayList<String[]>();

		for (int i = 0; i < attributeNames.length; i++) {
			String[] value = new String[2];
			value[0] = attributeNames[i];
			value[1] = values[i].toString();
			attributes.add(value);
		}
		
		return attributes;
	}
	
	
	public CellAttributeInformation createAttributes(Sheet sheet, int row, int column, CellAttributeInformation[][] cellInformation) {
		Cell cell = sheet.getCellForPosition(row, column);		
		
		Boolean leftBorder = ((column==0) || sheet.getCellForPosition(row, column-1).getContent().isEmpty()  );
		Boolean upperBorder = ((row==0) || sheet.getCellForPosition(row-1, column).getContent().isEmpty() );
		
		Boolean assocLegends = CellAttributeInformationUtil.hasAssocLegends(cellInformation, row, column);
		Boolean isBold = cell.getFont().IsBold();
		Boolean isItalic = cell.getFont().IsItalic();
		Boolean isUnderlined = cell.getFont().IsUnderlined();
			
		StructureType leftType = (column==0) ? StructureType.EMPTY : cellInformation[row][column-1].getCellType(); 
		StructureType upperType = (row==0) ? StructureType.EMPTY : cellInformation[row-1][column].getCellType();
		
		ContentValueType contentType = Util.identifyValueType(cell.getContent());
		
		return new CellAttributeInformation(leftBorder, upperBorder, assocLegends, isBold, isItalic, isUnderlined,
				leftType, upperType, contentType);
	}
	
	public CellAttributeInformation createLocalAttributes(Sheet sheet, int row, int column, StructureType type) {
		Cell cell = sheet.getCellForPosition(row, column);	
		Boolean leftBorder = ((column==0) || sheet.getCellForPosition(row, column-1).getContent().isEmpty()  );
		Boolean upperBorder = ((row==0) || sheet.getCellForPosition(row-1, column).getContent().isEmpty() );
		Boolean isBold = cell.getFont().IsBold();
		Boolean isItalic = cell.getFont().IsItalic();
		Boolean isUnderlined = cell.getFont().IsUnderlined();
		ContentValueType contentType = Util.identifyValueType(cell.getContent());
		
		return new CellAttributeInformation(type, leftBorder, upperBorder, isBold, isItalic, isUnderlined, contentType);
	
	}
	
}
