package info.kwarc.sally.core;

import java.util.List;

import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;

public class SallyInteractionTest {
	SallyInteraction interaction = new SallyInteraction();

	@SallyService
	public void Test(Integer i, SallyActionAcceptor acceptor, SallyContext context) {	
		acceptor.acceptResult("test");
	}

	@SallyService
	public void TestFalse(Integer i, SallyActionAcceptor acceptor) {
	}

	@SallyService
	public void TestFalse2(Float i, SallyActionAcceptor acceptor, Integer k) {	
	}

	@SallyService
	public void TestFalse3(Float i, Float acceptor, SallyContext k) {	
	}

	
	@Before
	public void test() {
		Assert.assertTrue(SallyActionAcceptor.class.isAssignableFrom(SallyActionAcceptor.class));
		interaction.registerServices(this);
		Assert.assertEquals(1, interaction.map.size());
	}
	
	@Test
	public void test2() {
		List<String> results = interaction.getPossibleInteractions(3, String.class);
		Assert.assertEquals(1, results.size());
		Assert.assertEquals("test", results.get(0));
	}

}
