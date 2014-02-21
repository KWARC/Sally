package info.kwarc.sally.spreadsheet3.extraction;

import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

/**
 * A class to represent a cell with layout information.
 * @author cliguda
 *
 */
public class Cell {
	CellSpaceInformation position;
	String content;
	String formula;
	int backgroundColor;
	Font font;
	CellBorder border;
	Boolean isHidden;
	
	
	public Cell(CellSpaceInformation position, String content, String formula, int backgroundColor,
			Font font, CellBorder border) {
		super();
		this.position = position;
		this.content = content;
		this.formula = formula;
		this.backgroundColor = backgroundColor;
		this.font = font;
		this.border = border;
		this.isHidden = false;
	}
	
	public Cell(CellSpaceInformation position) {
		super();
		this.position = position;
		this.isHidden = true;
	}

	public String getContent() {
		return content;
	}

	public String getFormula() {
		return formula;
	}

	public int getBackgroundColor() {
		return backgroundColor;
	}

	public CellSpaceInformation getPosition() {
		return position;
	}

	public Font getFont() {
		return font;
	}

	public CellBorder getBorder() {
		return border;
	}
	
	public Boolean isHidden() {
		return isHidden;
	}
	
	public void isHidden(Boolean value) {
		this.isHidden = value;
	}
	
	
}
