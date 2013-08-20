package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import java.util.HashMap;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

public class ValueInterpretationTest {
	ValueInterpretation vi;
	

	@Before
	public void setUp() throws Exception {
		Map<Integer, String> subExpressions = new HashMap<Integer,String>();
		subExpressions.put(new Integer(1), "\\d+");
		subExpressions.put(new Integer(2), "\\p{Alpha}");
		vi = new ValueInterpretation("M#1-#2", subExpressions, "@(I@[<rvar num=\"1\"/>,<rvar num=\"2\"/>])");
	}

	@Test
	public void test() {
		assertTrue(vi.isInterpretable("M126-a"));
		assertFalse(vi.isInterpretable("M126-aa"));
		assertFalse(vi.isInterpretable("126-a"));
		assertFalse(vi.isInterpretable("M12d-a"));
		assertFalse(vi.isInterpretable("M126+a"));
		assertEquals("@(I@[126,a])", vi.getValueInterpretation("M126-a"));
		assertEquals("", vi.getValueInterpretation("M126-aa"));
	}

}
