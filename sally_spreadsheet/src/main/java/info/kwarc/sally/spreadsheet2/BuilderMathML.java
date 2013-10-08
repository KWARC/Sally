package info.kwarc.sally.spreadsheet2;

public class BuilderMathML extends BuilderML {

	@Override
	String getVIVaribale(int i) {
		return "<rvar num=\"" + i + "\"/>";
	}

	@Override
	String getIdentifier(String s) {
		return "<ci>" + s + "</ci>";
	}

	@Override
	String getMathTagBegin() {
		return "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">";
	}
	
	@Override
	String getMathTagEnd() {
		return "</math>";
	}
	
	@Override
	String getOperatorApplication(String cd, String symbol) {
		return "<apply>\n<csymbol cd=\"" + cd + "\">" + symbol + "</csymbol>";
	}

	@Override
	String getApplicationEnd() {
		return "</apply>";
	}

}
