package info.kwarc.sally.core;

import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;

import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public class SallyInteractionTest {
	SallyInteraction interaction = new SallyInteraction();

	@SallyService
	public void Test(Integer i, SallyInteractionResultAcceptor acceptor, SallyContext context) {	
		acceptor.acceptResult("test");
	}

	@SallyService
	public void TestFalse(Integer i, SallyInteractionResultAcceptor acceptor) {
	}

	@SallyService
	public void TestFalse2(Float i, SallyInteractionResultAcceptor acceptor, Integer k) {	
	}

	@SallyService
	public void TestFalse3(Float i, Float acceptor, SallyContext k) {	
	} 
	
	@Before
	public void test() {
		Assert.assertTrue(SallyInteractionResultAcceptor.class.isAssignableFrom(SallyInteractionResultAcceptor.class));
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
