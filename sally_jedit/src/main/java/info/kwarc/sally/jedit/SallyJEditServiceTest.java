package info.kwarc.sally.jedit;

import info.kwarc.sally.core.SallyInteraction;

import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import sally.FileRef;
import sally.TextNotification;

public class SallyJEditServiceTest {

	ITextBuffer b;
	SallyInteraction i;
	
	FileRef dummyFile;

	String fileContents = "\\section{Doign comments}\n\nIn this section I want to show how commenting can work.\n\n\\subsection{Types of relations}\n\nThere are several types of relations.\n\n\\subsection{Subsections give lots of headaches}\n\n\\section{Differentiating between sections}\n\nis not a trivial task!\n";
	
	@Before
	public void setup() {
		dummyFile = FileRef.newBuilder().setResourceURI("text.txt").setMime("application/stex").build();
		
		i = new SallyInteraction();
		b = new ITextBuffer() {
			public String getPath() {
				return dummyFile.getResourceURI();
			}
			
			public String getText() {
				return fileContents;
			}
			
			public void addMarker(int line, String text) {
				System.out.println(String.format("Added Marker at line %d with text %s", line, text));
			}

			public void addOnChangeListener(Runnable runnable) {
				
			}

		};		
		i.registerServices(new SallyJEditService(b, i));
		i.registerServices(new ReferencingService());
	}

	@Test
	public void test() {
		List<TextNotification> notifications = i.getPossibleInteractions("/get/semantics", dummyFile, TextNotification.class);
		Assert.assertEquals(4, notifications.size());
	}

	@Test
	public void test2() {
		
	}
}
