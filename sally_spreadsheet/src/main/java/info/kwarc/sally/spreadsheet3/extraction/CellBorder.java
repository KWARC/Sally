package info.kwarc.sally.spreadsheet3.extraction;


/**
 * A class to represent the cell borders (top, bottom, left, right) for a cell.
 * @author cliguda
 *
 */
public class CellBorder {
	BorderLine top, bottom, left, right;

	public CellBorder(BorderLine top, BorderLine bottom, BorderLine left,
			BorderLine right) {
		super();
		this.top = top;
		this.bottom = bottom;
		this.left = left;
		this.right = right;
	}

	public BorderLine getTop() {
		return top;
	}

	public BorderLine getBottom() {
		return bottom;
	}

	public BorderLine getLeft() {
		return left;
	}

	public BorderLine getRight() {
		return right;
	}
	
}
