package info.kwarc.sissi.bpm.tasks;

import org.junit.Assert;
import org.junit.Test;

import sally.StartSubTask;

public class HandlerUtilsTest {

	@Test
	public void testSetCallbackTokenToMessage() {
		StartSubTask t = StartSubTask .newBuilder().setWorkflowID("test").build();
		t = (StartSubTask ) HandlerUtils.setCallbackTokenToMessage(t, 12L);
		Assert.assertEquals(12L, t.getCallbackToken());;
	}

}
