package info.kwarc.sally.spreadsheet3.extraction;

/**
 * A class to represent the font of a cell.
 * @author cliguda
 *
 */
public class Font {
	String fontName;
	int fontColor;
	float fontSize;
	Boolean isItalic;
	short isBold;
	short isUnderlined;
	
	public Font(String fontName, int fontColor, float fontSize, Boolean isItalic,
			short isBold, short isUnderlined) {
		super();
		this.fontName = fontName;
		this.fontColor = fontColor;
		this.fontSize = fontSize;
		this.isItalic = isItalic;
		this.isBold = isBold;
		this.isUnderlined = isUnderlined;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + fontColor;
		result = prime * result
				+ ((fontName == null) ? 0 : fontName.hashCode());
		result = prime * result + Float.floatToIntBits(fontSize);
		result = prime * result + isBold;
		result = prime * result
				+ ((isItalic == null) ? 0 : isItalic.hashCode());
		result = prime * result + isUnderlined;
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Font other = (Font) obj;
		if (fontColor != other.fontColor)
			return false;
		if (fontName == null) {
			if (other.fontName != null)
				return false;
		} else if (!fontName.equals(other.fontName))
			return false;
		if (Float.floatToIntBits(fontSize) != Float
				.floatToIntBits(other.fontSize))
			return false;
		if (isBold != other.isBold)
			return false;
		if (isItalic == null) {
			if (other.isItalic != null)
				return false;
		} else if (!isItalic.equals(other.isItalic))
			return false;
		if (isUnderlined != other.isUnderlined)
			return false;
		return true;
	}

	public String getFontName() {
		return fontName;
	}

	public int getFontColor() {
		return fontColor;
	}

	public float getFontSize() {
		return fontSize;
	}

	public Boolean IsItalic() {
		return isItalic;
	}

	public Boolean IsBold() {
		return (isBold > 0);
	}

	public Boolean IsUnderlined() {
		return (isUnderlined > 0);
	}
	
}
