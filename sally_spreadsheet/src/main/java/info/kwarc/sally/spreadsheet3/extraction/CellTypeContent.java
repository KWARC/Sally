package info.kwarc.sally.spreadsheet3.extraction;

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
