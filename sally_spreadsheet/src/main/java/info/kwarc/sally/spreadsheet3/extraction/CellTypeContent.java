package info.kwarc.sally.spreadsheet3.extraction;

/**
 * A class to hold information about the type, content and formula of a cell.
 * @author cliguda
 *
 */
public class CellTypeContent {
	
	int cellType;
	String content, formula;
	
	public CellTypeContent(int cellType, String content, String formula) {
		super();
		this.cellType = cellType;
		this.content = content;
		this.formula = formula;
	}

	public int getCellType() {
		return cellType;
	}

	public String getContent() {
		return content;
	}
	
	public String getFormula() {
		return formula;
	}

}
