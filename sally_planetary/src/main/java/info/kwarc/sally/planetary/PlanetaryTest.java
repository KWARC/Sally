package info.kwarc.sally.planetary;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public class PlanetaryTest {
	Planetary p;
	
	@Before
	public void setup() {
		p = new Planetary("http://localhost/drupal_planetary", "sally", "test", "123");
		
	}
	
	@Test
	public void testConnect() throws Exception {
		//String cookie = p.getSessionCookie();
		//Assert.assertTrue(cookie.length()>0);
	}
	
	@Test
	public void testGetURI() {
		System.out.println(p.getDefinitionLookupURL("https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?ISOhexbolt"));
	}

}
