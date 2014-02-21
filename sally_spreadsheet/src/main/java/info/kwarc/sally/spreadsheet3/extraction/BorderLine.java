package info.kwarc.sally.spreadsheet3.extraction;

/**
 * A class to represent a cell border either from Excel or OpenOffice
 * @author cliguda
 *
 */
public class BorderLine {
	
	public enum FormatStyle {
		EXCELSTYLE, OPENOFFICESTYLE
	}
	
	public enum ExcelBorderStyle {
		NONE, DOT, DASH_DOT_DOT, DASH_DOT, DASH, CONTINUOUS, DOUBLE, SLANT_DASH_DOT
	}
	
	public enum ExcelBorderWeight {
		HAIRLINE, THIN, MEDIUM, THICK
	}

	long borderColor;
	FormatStyle formatStyle;
	ExcelBorderStyle excelBorderStyle;
	ExcelBorderWeight excelBorderWeight;
	
	int ooInnerLineWidth;
	int ooOuterLineWidth;
	int ooLineDistance;
	
	/**
	 * Constructor for a borderline from an Excel cell.
	 */
	public BorderLine(long borderColor, FormatStyle formatStyle,
			ExcelBorderStyle excelBorderStyle, ExcelBorderWeight excelBorderWeight) {
		super();
		if (formatStyle != FormatStyle.EXCELSTYLE)
			throw new java.lang.IllegalArgumentException("ExcelStyle Constructur for non ExcelStyle BorderLine.");
		
		this.borderColor = borderColor;
		this.formatStyle = formatStyle;
		this.excelBorderStyle = excelBorderStyle;
		this.excelBorderWeight = excelBorderWeight;
	
		this.ooInnerLineWidth = -1;
		this.ooOuterLineWidth = -1;
		this.ooLineDistance = -1;
	}

	/**
	 * Constructor for a borderline from an OpenOffice cell.
	 */
	public BorderLine(long borderColor, FormatStyle formatStyle,
			int ooInnerLineWidth, int ooOuterLineWidth, int ooLineDistance) {
		super();
		if (formatStyle != FormatStyle.OPENOFFICESTYLE)
			throw new java.lang.IllegalArgumentException("OOStyle Constructur for non OOStyle BorderLine.");
		
		this.borderColor = borderColor;;
		this.formatStyle = formatStyle;
		
	
		this.ooInnerLineWidth = ooInnerLineWidth;
		this.ooOuterLineWidth = ooOuterLineWidth;
		this.ooLineDistance = ooLineDistance;
		
		this.excelBorderStyle = null;
		this.excelBorderWeight = null;
	}

	public long getBorderColor() {
		return borderColor;
	}

	public FormatStyle getFormatStyle() {
		return formatStyle;
	}

	public ExcelBorderStyle getExcelBorderStyle() {
		return excelBorderStyle;
	}

	public ExcelBorderWeight getExcelBorderWeight() {
		return excelBorderWeight;
	}

	public int getOoInnerLineWidth() {
		return ooInnerLineWidth;
	}

	public int getOoOuterLineWidth() {
		return ooOuterLineWidth;
	}

	public int getOoLineDistance() {
		return ooLineDistance;
	}
	
	public Boolean isSmallerOrEqualThen(BorderLine borderline) {
		if ((this.getFormatStyle() == FormatStyle.EXCELSTYLE) && (borderline.formatStyle == FormatStyle.EXCELSTYLE)) {
			if (this.getExcelBorderWeight().ordinal() < borderline.getExcelBorderWeight().ordinal())
				return true;
			else if (this.getExcelBorderWeight().ordinal() > borderline.getExcelBorderWeight().ordinal())
				return false;
			else {
				return (this.getExcelBorderStyle().ordinal() <= borderline.getExcelBorderStyle().ordinal());
			}
		} else if ((this.getFormatStyle() == FormatStyle.OPENOFFICESTYLE) && (borderline.formatStyle == FormatStyle.OPENOFFICESTYLE)) {
			return ((this.getOoInnerLineWidth() <= borderline.getOoInnerLineWidth()) && (this.getOoOuterLineWidth() <= borderline.getOoOuterLineWidth()) &&
					(this.getOoLineDistance() <= borderline.getOoLineDistance()) );
		} else
			return false;
	}
	
}
