package info.kwarc.sally.spreadsheet2;


import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Util {
	
	static Pattern omdocUriPattern = Pattern.compile("omdoc://(.+)#(.+)");
	static Pattern cellAddressPattern = Pattern.compile("([A-Z]+)([0-9]+)");
	
	
	public static String getCDFromURI(String uri) {
		Matcher matcher = omdocUriPattern.matcher(uri);
		if (matcher.matches())
			return matcher.group(1);
		else
			return "";
	}
	
	public static String getSymbolFromURI(String uri) {
		Matcher matcher = omdocUriPattern.matcher(uri);
		if (matcher.matches())
			return matcher.group(2);
		else
			return "";
	}
	
}
