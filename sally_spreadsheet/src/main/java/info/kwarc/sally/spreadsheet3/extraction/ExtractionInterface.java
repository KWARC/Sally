package info.kwarc.sally.spreadsheet3.extraction;


import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import psf.ParserParameter;

public class ExtractionInterface {
	//This works fine when you run it with mvn jetty:run, but fails with the packaged war
	final String process = System.getProperty("user.dir") + "/src/main/resources/info/kwarc/sally/spreadsheet3/extraction/ModelApplication.rmp";
	//final String  process ="D:\\Projects\\sissi\\trunk\\sally3\\src\\main\\resources\\info\\kwarc\\sissi\\model\\extraction\\ModelApplication.rmp";
	final String model = System.getProperty("user.dir") + "\\src\\main\\resources\\info\\kwarc\\sally\\spreadsheet3\\extraction\\models\\DTOptimized.model";
	final String evalDir = System.getProperty("user.dir") + "\\src\\main\\resources\\info\\kwarc\\sally\\spreadsheet3\\extraction\\evaluation\\";
	
	final static Logger logger = LoggerFactory.getLogger(ExtractionInterface.class);
	final static psf.ParserInterface parser = new psf.ParserInterface();
	
	CellClassifier classifier;
	Map<Integer, BorderLine.ExcelBorderStyle> convert;
	
	public ExtractionInterface() {
		classifier = new CellClassifier(process, model, CellAttributeInformation.getAttributes());
		logger.debug("Rapidminer interface was set up.");
		convert = new HashMap<Integer, BorderLine.ExcelBorderStyle>();
		convert.put(0, BorderLine.ExcelBorderStyle.NONE);
		convert.put(1, BorderLine.ExcelBorderStyle.CONTINUOUS);
		convert.put(2, BorderLine.ExcelBorderStyle.DASH);
		convert.put(3, BorderLine.ExcelBorderStyle.DASH_DOT);
		convert.put(4, BorderLine.ExcelBorderStyle.DASH_DOT_DOT);
		convert.put(5, BorderLine.ExcelBorderStyle.DOT);
		convert.put(6, BorderLine.ExcelBorderStyle.DOUBLE);
		convert.put(7, BorderLine.ExcelBorderStyle.SLANT_DASH_DOT);
	}
	
	
	public ParsingResult extractStructures(List<Sheet> sheets, ExtractionParameter parameter) throws FileNotFoundException {
		/*logger.debug("Start extracting abstract structures from dataMsg...");
		sally.ParsingResultMsg.Builder parsingResults = sally.ParsingResultMsg.newBuilder();
		
		List<Sheet> sheets = converDataMessage(dataMsg);
		ExtractionParameter parameter = convertParameter(dataMsg);
		*/
		ParsingResult result = new ParsingResult();
		int startIndex = 0;
		for (Sheet sheet : sheets) {
			
			// Testing for an empty sheet
			boolean emptySheet = true;
			for (int i = 0; i < sheet.getMaxRow(); i++)
				for (int j = 0; j < sheet.getMaxColumn(); j++)
					if ((sheet.getCellForPosition(i, j) != null) && (!sheet.getCellForPosition(i, j).getContent().isEmpty()) )
						emptySheet = false;
			
			if (!emptySheet) {
				/*
				logger.debug("Start extracting abstract structures for sheet with id " + sheet.getId());
				logger.debug("Spreadsheet content:");
				for (int row = 0; row < sheet.getMaxRow(); row++) {
					String content = "";
					for (int column = 0; column < sheet.getMaxColumn(); column++) {
						content += "(" + row + "/" + column + ") " + " " + sheet.getCellForPosition(row, column).getContent() + " | ";
					}
					logger.debug(content);
					System.out.println();
				}*/
				
				// Parsing of all formula not unified
				Map<CellSpaceInformation, psf.ParserResult> cellFormula = new HashMap<CellSpaceInformation, psf.ParserResult>();
				for (int row = 0; row < sheet.getMaxRow(); row++) {
					for (int column = 0; column < sheet.getMaxColumn(); column++) {
						Cell cell = sheet.getCellForPosition(row, column); 
						if ((cell != null) && !cell.getFormula().isEmpty()) {
							//psf.ParserResult formula = parser.parseFormula(cell.getFormula(), "", true, true, false);
							psf.ParserResult formula = parser.parseFormula(new ParserParameter(cell.getFormula(), sheet.getId(), false, false, false, true, null));
				
							cellFormula.put(new CellSpaceInformation(sheet.getId(), row, column), formula);
						}
					}
				}
				
				logger.debug("Classification:");
				CellAttributeInformation[][] cellAttributes = classifier.classify(sheet, parameter, cellFormula);
				
				for (int row = 0; row < sheet.getMaxRow(); row++) {
					String classification = "";
					for (int column = 0; column < sheet.getMaxColumn(); column++) {
						classification += "(" + row + "/" + column + ") " + " [";
						if (cellAttributes[row][column].getCellType() == StructureType.FB)
							classification += "FB";
						else if (cellAttributes[row][column].getCellType() == StructureType.LEGEND)
							classification += "LE";
						else if (cellAttributes[row][column].getCellType() == StructureType.LEGENDHEADER)
							classification += "LH";
						else if (cellAttributes[row][column].getCellType() == StructureType.EMPTY)
							classification += "E";
						else if (cellAttributes[row][column].getCellType() == StructureType.HIDDEN)
							classification += "H";
						classification += "] | ";
					} 
					logger.debug(classification);
				}
				
				FeatureMaps features = new FeatureMaps(sheet.getMaxRow(), sheet.getMaxColumn());
				if (parameter.isColorAsStructure())
					AreaExtraction.markMapByColor(sheet, features.createMap("Color Map"));
				else
					AreaExtraction.markMapUniform(sheet, features.createMap("Color Map"));
				
				if (parameter.isBorderAsStructure())
					AreaExtraction.markMapByBorder(sheet, features.createMap("Border Map"));
				else
					AreaExtraction.markMapUniform(sheet, features.createMap("Border Map"));
				
				if (parameter.isFontAsStructure())
					AreaExtraction.markMapByFont(sheet, features.createMap("Font Map"));
				else
					AreaExtraction.markMapUniform(sheet, features.createMap("Font Map"));
				
				// Parsing of all formula unified
				cellFormula = new HashMap<CellSpaceInformation, psf.ParserResult>();
				for (int row = 0; row < sheet.getMaxRow(); row++) {
					for (int column = 0; column < sheet.getMaxColumn(); column++) {
						Cell cell = sheet.getCellForPosition(row, column); 
						if ((cell != null) && !cell.getFormula().isEmpty()) {
							//psf.ParserResult formula = parser.parseFormula(cell.getFormula(), "", true, true, false);
							psf.ParserResult formula = parser.parseFormula(new ParserParameter(cell.getFormula(), sheet.getId(), true, true, false, false, null));
				
							cellFormula.put(new CellSpaceInformation(sheet.getId(), row, column), formula);
						}
					}
				}
				AreaExtraction.markMapByFormulae(sheet, features.createMap("Formulae Map"), cellFormula);
				
				//System.out.println("Maps");
				//features.printAllMaps();
				
				//features.printAllMaps();
				AEResults aeResults = AreaExtraction.extractAreas(sheet, sheet.getId(), startIndex, cellAttributes, features);
				result.addAEResult(aeResults);
				startIndex = aeResults.getMaxIndex() + 1;
				
				/*String filename = dataMsg.getFileName();
				if (filename.contains("/"))
					filename = filename.substring(filename.lastIndexOf("/"));
				if (filename.contains("\\"))
					filename = filename.substring(filename.lastIndexOf("\\"));
				PrintWriter evalOut = new PrintWriter(new File(evalDir + filename + ".sam"));
				
				aeResults.print(evalOut);*/
				
				List<AffiliationInformation> affInfos =  AffiliationInformationExtraction.extract(aeResults);
				result.addAllAffiliationInformation(affInfos);
				/*evalOut.println("Affiliation Information:");
				for (AffiliationInformation ai : affInfos) {
					String affMsg = "";
					affMsg += ai.getId() + " is affiliated to ";
					for (Integer id : ai.getAffiliatedIds())
						affMsg += id + " / ";
					evalOut.println(affMsg);
				}
				
				evalOut.close();*/
				
				/*for (AreaInformation ai : aeResults.getAreas())
					parsingResults.addAreas(ai.getProtoBufRepresentation());
				for (AmbiguousInformation ambig : aeResults.getAmbiguous())
					parsingResults.addAmbig(ambig.getProtoBufRepresentation());
				for (AffiliationInformation affInfo : affInfos) 
					parsingResults.addAffiliation(affInfo.getProtoBufRepresentation());*/
			}
		}
		
		return result;
	}
	
	/*private List<Sheet> converDataMessage(sally.Data dataMsg) {
		List<Sheet> sheets = new ArrayList<Sheet>();
		
		for (sally.Sheet sheetMsg : dataMsg.getSheetsList()) 
			sheets.add(convertSheetMessage(sheetMsg));
		
		return sheets;
	}
	
	private Sheet convertSheetMessage(sally.Sheet sheetMsg) {
		Sheet sheet = new Sheet(sheetMsg.getId());
		for (sally.Cell cellMsg : sheetMsg.getCellsList()) {
			sheet.addCell(convertCellMessage(cellMsg));
		}
		return sheet;
	}
	
	private Cell convertCellMessage(sally.Cell cellMsg) {
		return new Cell(new CellSpaceInformation(cellMsg.getData().getPosition()), cellMsg.getData().getValue(), cellMsg.getData().getFormula(),
				cellMsg.getBackColor(), convertFontMessage(cellMsg.getFont()), convertBorderMessage(cellMsg.getBorder()) );
	}
	
	private Font convertFontMessage(sally.Font fontMsg) {
		return new Font(fontMsg.getFontName(), fontMsg.getFontColor(), fontMsg.getFontSize(),
				fontMsg.getIsItalic(), fontMsg.getIsBold(), fontMsg.getIsUnderlined());
	}
	
	private CellBorder convertBorderMessage(sally.CellBorder cellBorder) {
		return new CellBorder(convertBorderLineMessage(cellBorder.getTop()), 
				convertBorderLineMessage(cellBorder.getBottom()), convertBorderLineMessage(cellBorder.getLeft()), 
				convertBorderLineMessage(cellBorder.getRight()));
	}
	
	private BorderLine convertBorderLineMessage(sally.BorderLine borderLineMsg) {
		if (borderLineMsg.getFormatStyle() == 0) 
			return new BorderLine(borderLineMsg.getBorderColor(), 
					BorderLine.FormatStyle.values()[borderLineMsg.getFormatStyle()], 
					convert.get(borderLineMsg.getExcelBorderStyle()), 
					BorderLine.ExcelBorderWeight.values()[borderLineMsg.getExcelBorderWeight()]);
		else if (borderLineMsg.getFormatStyle() == 1)
			return new BorderLine(borderLineMsg.getBorderColor(), 
					BorderLine.FormatStyle.values()[borderLineMsg.getFormatStyle()],
					borderLineMsg.getOoInnerLineWidth(), borderLineMsg.getOoOuterLineWidth(), borderLineMsg.getOoLineDistance());
		else
			return null;
	}
	
	private ExtractionParameter convertParameter(sally.Data dataMsg) {
		sally.ParsingParameter parameter = dataMsg.getParameter();
		boolean textAsLegend =  parameter.getUseTextAsLegend();
		boolean colorAsStructure = parameter.getUseColorAsStructure();
		boolean borderAsStructure = parameter.getUseBorderAsStructure();
		boolean fontAsStructure = parameter.getUseFontAsStructure();
		
		return new ExtractionParameter(textAsLegend, colorAsStructure, borderAsStructure, fontAsStructure);
	}*/

}
