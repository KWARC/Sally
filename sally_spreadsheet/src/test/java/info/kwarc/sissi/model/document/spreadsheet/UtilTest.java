package info.kwarc.sissi.model.document.spreadsheet;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;


public class UtilTest {

	@Before
	public void setUp() throws Exception {
	}

	@Test
	public void testIdentifyValueType() {
		Assert.assertEquals("ValueType Empty", ContentValueType.EMPTY, Util.identifyValueType(""));
		Assert.assertEquals("ValueType String", ContentValueType.STRING_NUMBER, Util.identifyValueType("Test"));
		Assert.assertEquals("ValueType Int", ContentValueType.STRING_NUMBER, Util.identifyValueType("1984"));
		Assert.assertEquals("ValueType Float", ContentValueType.FLOAT, Util.identifyValueType("6.481"));
	}
	
	@Test
	public void testConvertRangeCharacter() {
		Assert.assertEquals("A", 0, Util.convertRangeCharacter("A"));
		Assert.assertEquals("Z", 25, Util.convertRangeCharacter("Z"));
		Assert.assertEquals("AA", 26, Util.convertRangeCharacter("AA"));
		Assert.assertEquals("AZ", 51, Util.convertRangeCharacter("AZ"));
		Assert.assertEquals("BA", 52, Util.convertRangeCharacter("BA"));
		Assert.assertEquals("ZZ", 701, Util.convertRangeCharacter("ZZ")); // 26^2+25
		Assert.assertEquals("AAA", 702, Util.convertRangeCharacter("AAA")); // 26^2+26
	}
	
	@Test
	public void testConvertIndex2RangeCharacter() {
		Assert.assertEquals("A", "A", Util.convertIndex2RangeCharacter(0));
		Assert.assertEquals("Z", "Z", Util.convertIndex2RangeCharacter(25));
		Assert.assertEquals("AA", "AA", Util.convertIndex2RangeCharacter(26));
		Assert.assertEquals("AZ", "AZ", Util.convertIndex2RangeCharacter(51));
		Assert.assertEquals("BA", "BA", Util.convertIndex2RangeCharacter(52));
		Assert.assertEquals("ZZ", "ZZ", Util.convertIndex2RangeCharacter(701)); 
		Assert.assertEquals("AAA", "AAA", Util.convertIndex2RangeCharacter(702));
	}
	
	@Test
	public void testIsString() {
		Assert.assertTrue(Util.isString("Ein test"));
		Assert.assertTrue(Util.isString("Ein test und 842 Zahlen !"));
		Assert.assertFalse(Util.isString("102"));
		Assert.assertFalse(Util.isString("102a"));
		Assert.assertFalse(Util.isString("1.0.2"));
	}

}
