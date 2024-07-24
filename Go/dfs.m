global a;
a =zeros(1,5);
dfss(1);

function dfss(t)
    global a;
    if (t>5)
        disp(a);
        return;
    end
    for i =1 : 5
        a(t) = i;
        dfss(t+1)
    end
end
