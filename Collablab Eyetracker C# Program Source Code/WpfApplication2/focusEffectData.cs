using System;

/// <summary>
/// focusEffectData stores three attributes: x, y, and starting time.
/// </summary>
public class focusEffectData
{
    public int x, y;
    public DateTime startTime;
    public System.Windows.Shapes.Rectangle rect;
    public focusEffectData(int x_input, int y_input, DateTime startTime_input, System.Windows.Shapes.Rectangle rect_input)
	{
        x = x_input;
        y = y_input;
        startTime = startTime_input;
        rect = rect_input;
	}
}
