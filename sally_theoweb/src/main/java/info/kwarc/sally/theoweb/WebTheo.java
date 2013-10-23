package info.kwarc.sally.theoweb;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.comm.CallbackManager;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.IAbstractMessageRunner;
import info.kwarc.sally.core.theo.CookieProvider;
import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.theo.ScreenCoordinatesProvider;
import info.kwarc.sally.core.theo.Theo;

import java.util.HashSet;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.Cookie;
import sally.SallyFrameChoice;
import sally.SallyFrameList;
import sally.SallyFrameResponse;
import sally.SallyFrameService;
import sally.ScreenCoordinates;
import sally.TheoOpenWindow;

import com.google.inject.Inject;
import com.google.protobuf.AbstractMessage;

public class WebTheo implements Theo {

	CallbackManager manager;
	ScreenCoordinatesProvider coordProvider;
	CookieProvider cookieProvider;
	Logger log;
	
	@Inject
	public WebTheo(CallbackManager manager, ScreenCoordinatesProvider coordProvider, CookieProvider cookieProvider) {
		this.manager = manager;
		this.coordProvider = coordProvider;
		this.cookieProvider = cookieProvider;
		this.log = LoggerFactory.getLogger(getClass());
	}

	@Override
	public void letUserChoose(DocumentInformation sender, final List<SallyMenuItem> menuItems) {

		HashSet<String> frames=  new HashSet<String>();
		for (SallyMenuItem menuItem : menuItems) {
			frames.add(menuItem.getFrame());
		}

		SallyFrameList.Builder  frameList = SallyFrameList.newBuilder();
		for (String frame : frames) {
			SallyFrameResponse.Builder frameResponse =SallyFrameResponse.newBuilder().setFrameName(frame);
			for (SallyMenuItem menuItem : menuItems) {
				if (!menuItem.getFrame().equals(frame))
					continue;
				frameResponse.addFrameServices(SallyFrameService.newBuilder()
						.setDescription(menuItem.getExplanation())
						.setName(menuItem.getService())
						.setId(menuItem.hashCode())
						.build()
						);
			}
			frameList.addFrames(frameResponse.build());
		}
		log.info("Sending frames "+frameList);
		frameList.setFileName(sender.getFileName());

		Long callbackID = manager.registerCallback(new IAbstractMessageRunner() {

			@Override
			public void run(AbstractMessage m) {
				SallyFrameChoice choice = (SallyFrameChoice) m;
				for (SallyMenuItem item : menuItems) {
					if (item.hashCode() == choice.getChoiceId()) {
						item.run();
					}
				}
			}
		});

		frameList.setCallbackToken(callbackID);
		sender.getNetworkSender().sendMessage("/theo/letuserchoose", frameList.build());
	}

	@Override
	public int openWindow(DocumentInformation sender, String title, String URL, int sizeX, int sizeY) {
		Coordinates coords = coordProvider.getRecommendedPosition();
		Cookie cookies = Cookie.newBuilder().setCookie(cookieProvider.getCookies()).setUrl(cookieProvider.getUrl()).build();
		
		TheoOpenWindow openRequest = 
				TheoOpenWindow.newBuilder().setSizeX(sizeX).setSizeY(sizeY).setTitle(title).setUrl(URL)
					.setPosition(ScreenCoordinates.newBuilder().setX(coords.getX()).setY(coords.getY()).build())
					.setCookie(Cookie.newBuilder().setCookie(cookies.getCookie()).setUrl(cookies.getUrl()).build())
					.build();
		
		sender.getNetworkSender().sendMessage("/theo/newWindow", openRequest);
		return 0;
	}

	@Override
	public void updateWindow(DocumentInformation sender,int windowID, String title,
			String URL, Integer sizeX, Integer sizeY) {
		// TODO Auto-generated method stub

	}

	@Override
	public void closeWindow(DocumentInformation sender, int windowID) {
		// TODO Auto-generated method stub

	}

}
