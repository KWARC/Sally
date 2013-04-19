package info.kwarc.sally.theofx;

import info.kwarc.sally.core.SallyMenuItem;

import java.util.ArrayList;
import java.util.List;

public class TheoServiceTest {

	public static void main(String[] args) {
		TheoService q = new TheoService();
		List<SallyMenuItem> items = new ArrayList<SallyMenuItem>();
		items.add(new SallyMenuItem("Knowledge", "Definition Lookup") {
			
			public void run() {
				System.out.println("Def look");
			}
		});
		items.add(new SallyMenuItem("Knowledge", "Semantic Nav") {
			
			public void run() {
				System.out.println("semantic nav");
			}
		});
		
		SallyMenuItem item = q.letUserChoose(items);
		item.run();
	}
}
