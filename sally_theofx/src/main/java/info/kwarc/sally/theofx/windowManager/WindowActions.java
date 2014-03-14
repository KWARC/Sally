package info.kwarc.sally.theofx.windowManager;

import com.sun.jna.platform.win32.User32;
import com.sun.jna.platform.win32.WinDef.HWND;

public class WindowActions {

	//May need to check things other than the name of the name of the desktop to cover a broader range of desktop platforms
	/**
	 * @param processName e.g. excel
	 * @param filenameWithoutPath e.g. Book1
	 * */
	public static void bringToFront(String processName, String filenameWithoutPath){
		String desktop = new OSDiagnostics().Desktop; 
		String windowsTitle="";
		if (processName.equals("excel")){
			windowsTitle = "Microsoft Excel - "+filenameWithoutPath; 
		}
		if (desktop.equals("windows")){
			bringToFrontForWindows(processName, windowsTitle);
		}
	}

	private static void bringToFrontForWindows(String processName, String windowsTitle){
		User32 user32 = TheoWin32.instance;
		HWND hWnd = user32.FindWindow(null, windowsTitle);
		user32.ShowWindow(hWnd, User32.SW_SHOW);
		user32.SetForegroundWindow(hWnd);
	}

}
