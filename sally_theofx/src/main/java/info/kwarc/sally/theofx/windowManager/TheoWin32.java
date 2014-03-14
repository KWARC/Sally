package info.kwarc.sally.theofx.windowManager;

import com.sun.jna.Native;
import com.sun.jna.platform.win32.User32;
import com.sun.jna.platform.win32.WinDef.HWND;
import com.sun.jna.win32.W32APIOptions;

//from coderanch and some googled places

public interface TheoWin32 extends W32APIOptions
{
	User32 instance = (User32) Native.loadLibrary("user32", User32.class, DEFAULT_OPTIONS);
	boolean ShowWindow (HWND hWnd, int nCmdShow);
	boolean SetForegroundWindow(HWND hWnd);
	HWND FindWindow(String winClass, String title);
}
