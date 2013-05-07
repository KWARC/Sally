package info.kwarc.sally.theoxul;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.ScreenCoordinates;
import sally.TheoOpenWindow;
import sally.WhoAmI;

public class TheoService {

	SallyMenuItem chosenItem;
	ScreenCoordinates coords;
	String xulRunnerPath;
	String applicationPath;
	Logger log;
	String theoInstance;
	
	public TheoService(String xulRunnerPath, String applicationPath) {
		log = LoggerFactory.getLogger(getClass());
		theoInstance = null;
	}

	@SallyService(channel="/service/theo/register")
	public void registerTheo(WhoAmI whoami, SallyActionAcceptor acceptor, SallyContext context) {
		if (theoInstance == null) {
			System.out.println("Got a theo!!!");
			acceptor.acceptResult(true);
			theoInstance = "true";
		}
	}
	
	@SallyService
	public void openWindow(TheoOpenWindow newWindow, SallyActionAcceptor acceptor, SallyContext context) {
	}
	
}
