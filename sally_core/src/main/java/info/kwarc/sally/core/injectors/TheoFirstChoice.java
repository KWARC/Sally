package info.kwarc.sally.core.injectors;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.Theo;

import java.util.List;

import com.google.inject.AbstractModule;
import com.google.inject.Singleton;

public class TheoFirstChoice extends AbstractModule { 

	@Singleton
	static public class FirstChoiceTheoImpl implements Theo {

		@Override
		public SallyMenuItem letUserChoose(List<SallyMenuItem> menuItem) {
			if (menuItem == null || menuItem.size() == 0)
				return null;

			return menuItem.get(0);
		}

		@Override
		public int openWindow(Long inst, String title, String URL, int sizeX, int sizeY) {
			System.out.println("opening a window with title "+title+" at URL"+URL);
			return 0;
		}

		@Override
		public void updateWindow(int windowID, String title, String URL,
				Integer sizeX, Integer sizeY) {
		}

		@Override
		public void closeWindow(int windowID) {
			System.out.println("closing window windowID");
		}
	}
	
	

	@Override
	protected void configure() {
		bind(Theo.class).to(FirstChoiceTheoImpl.class);
	};

};
