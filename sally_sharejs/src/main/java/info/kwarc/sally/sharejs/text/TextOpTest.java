package info.kwarc.sally.sharejs.text;

import java.io.IOException;

import org.junit.Before;
import org.junit.Test;

import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;

public class TextOpTest {
	ObjectMapper mapper; 

	@Before
	public void setup() {
		mapper = new ObjectMapper();
	}
	
	@Test
	public void test() {
		String op = "{\"op\":[8,\" everyone!\"],\"v\":1}";
		try {
			TextOp textop = mapper.readValue(op, TextOp.class);
		} catch (JsonParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (JsonMappingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

}
