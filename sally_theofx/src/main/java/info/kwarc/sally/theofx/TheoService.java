package info.kwarc.sally.theofx;

import info.kwarc.sally.core.CookieProvider;
import info.kwarc.sally.core.ScreenCoordinatesProvider;
import info.kwarc.sally.core.comm.Coordinates;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.Theo;

import java.awt.Dialog.ModalityType;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import javax.swing.AbstractButton;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;

import sally.Cookie;
import sally.TheoChangeWindow;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class TheoService implements Theo {

	SallyMenuItem chosenItem;
	HashMap<Integer, TheoWindow> openedWindows;
	Random r = new Random();
	ScreenCoordinatesProvider coordProvider;
	CookieProvider cookieProvider;
	
	@Inject
	public TheoService(ScreenCoordinatesProvider coordProvider, CookieProvider cookieProvider) {
		this.coordProvider = coordProvider;
		this.cookieProvider = cookieProvider;
		openedWindows = new HashMap<Integer, TheoWindow>();
	}
	
	public int openWindow(String title, String URL, int sizeX, int sizeY) {
		Integer resID = r.nextInt();
		Coordinates coords = coordProvider.getRecommendedPosition();
		Cookie cookies = Cookie.newBuilder().setCookie(cookieProvider.getCookies()).setUrl(cookieProvider.getUrl()).build();
		openedWindows.put(resID, TheoWindow.addWindow(sizeY, sizeX, coords.getX(), coords.getY(), title, URL, cookies, true));
		return resID;
	}

	public void changeWindow(TheoChangeWindow window) {
		if (!openedWindows.containsKey(window.getWindowid())) {
			return;
		}
		TheoWindow w = openedWindows.get(window.getWindowid());
		
		if (window.hasCookie()) {
			w.setCookie(window.getCookie().getUrl(), window.getCookie().getCookie());
		}
		
		if (window.hasUrl()) {
			w.changeURL(window.getUrl());
		}
	}
	
	public void closeWindow(int windowID) {
		TheoWindow wnd = openedWindows.get(windowID);
		if (wnd != null) {
			wnd.closeWindow();
		}
	}

	public SallyMenuItem letUserChoose(final List<SallyMenuItem> items) {
		final JFrame frame = new JFrame("FrameDemo");
		final JDialog dialog = new JDialog(frame, ModalityType.APPLICATION_MODAL);
		final JPanel t = new JPanel();
		chosenItem = null;
		
		t.setLayout(new BoxLayout(t, BoxLayout.PAGE_AXIS));
		
		ActionListener frameListener = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				String chosen = e.getActionCommand();
				t.removeAll();
				for (SallyMenuItem item : items) {
					if (item.getFrame().equals(chosen)) {
						final SallyMenuItem rr = item;
						JButton b = new JButton(item.getService());
						b.setHorizontalTextPosition(AbstractButton.CENTER);
						b.setActionCommand(item.getService());
						b.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent e) {	
								chosenItem = rr;
								dialog.setVisible(false);
							}
						});
						t.add(b);
					}
				}
				t.updateUI();
				dialog.pack();
				frame.pack();
			}
		};
		
		frame.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);
		Set<String> frames = new HashSet<String>();
		t.add(new JLabel("Please select the frame"));

		for (SallyMenuItem item : items) {
			if (frames.contains(item.getFrame()))
				continue;
			frames.add(item.getFrame());
			JButton b = new JButton(item.getFrame());
			b.setHorizontalTextPosition(AbstractButton.CENTER);
			b.setActionCommand(item.getFrame());
			b.addActionListener(frameListener);
			t.add(b);
		}

		Coordinates coords = coordProvider.getRecommendedPosition();
		
		dialog.setLocation(coords.getX(), coords.getY());
		dialog.setContentPane(t);
		dialog.pack();
		dialog.setVisible(true);
		frame.removeAll();
		frame.dispose();
				
		return chosenItem;
	}
}
