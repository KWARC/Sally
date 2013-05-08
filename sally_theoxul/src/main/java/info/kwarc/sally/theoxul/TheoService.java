package info.kwarc.sally.theoxul;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.networking.cometd.CometDSendRequest;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.ScreenCoordinates;
import sally.TheoOpenWindow;
import sally.WhoAmI;
import sally.WhoAmI.EnvironmentType;

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
		this.xulRunnerPath = xulRunnerPath;
		this.applicationPath = applicationPath;
	}

	@SallyService(channel="/service/theo/register")
	public void registerTheo(WhoAmI whoami, SallyActionAcceptor acceptor, SallyContext context) {
		if (whoami.getEnvironmentType() != EnvironmentType.Desktop)
			return;
		if (theoInstance == null) {
			theoInstance = context.getContextVar("senderID", String.class);
			acceptor.acceptResult(true);
		}
	}
	
	@SallyService
	public void openWindow(TheoOpenWindow newWindow, SallyActionAcceptor acceptor, SallyContext context) {
		if (theoInstance == null) {
			log.debug("No theo connected. Starting one.");
			(new Thread(new TheoRunner(xulRunnerPath, applicationPath))).start();
			for (int retry = 500; retry >= 0; retry --) {
				if (theoInstance == null) {
					try {
						Thread.sleep(200);
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
		}
		
		context.getCurrentInteraction().getOneInteraction(new CometDSendRequest(theoInstance, "/service/theo/newWindow", newWindow), Boolean.class);
	}
	
}
